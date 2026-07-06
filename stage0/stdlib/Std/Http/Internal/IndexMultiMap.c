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
lean_object* v_entries_258_; lean_object* v_indexes_259_; lean_object* v___x_260_; lean_object* v___f_261_; lean_object* v___x_262_; size_t v_sz_263_; size_t v___x_264_; lean_object* v_entries_265_; 
v_entries_258_ = lean_ctor_get(v_map_256_, 0);
lean_inc_ref(v_entries_258_);
v_indexes_259_ = lean_ctor_get(v_map_256_, 1);
lean_inc_ref(v_indexes_259_);
lean_dec_ref(v_map_256_);
v___x_260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_254_, v_inst_255_, v_indexes_259_, v_key_257_);
lean_dec_ref(v_indexes_259_);
lean_inc_n(v___x_260_, 2);
v___f_261_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_261_, 0, v___x_260_);
lean_closure_set(v___f_261_, 1, v_entries_258_);
v___x_262_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_263_ = lean_array_size(v___x_260_);
v___x_264_ = ((size_t)0ULL);
v_entries_265_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_262_, v___x_260_, v___f_261_, v_sz_263_, v___x_264_, v___x_260_);
lean_dec(v___x_260_);
return v_entries_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b2_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_map_270_, lean_object* v_key_271_, lean_object* v_h_272_){
_start:
{
lean_object* v_entries_273_; lean_object* v_indexes_274_; lean_object* v___x_275_; lean_object* v___f_276_; lean_object* v___x_277_; size_t v_sz_278_; size_t v___x_279_; lean_object* v_entries_280_; 
v_entries_273_ = lean_ctor_get(v_map_270_, 0);
lean_inc_ref(v_entries_273_);
v_indexes_274_ = lean_ctor_get(v_map_270_, 1);
lean_inc_ref(v_indexes_274_);
lean_dec_ref(v_map_270_);
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_268_, v_inst_269_, v_indexes_274_, v_key_271_);
lean_dec_ref(v_indexes_274_);
lean_inc_n(v___x_275_, 2);
v___f_276_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_276_, 0, v___x_275_);
lean_closure_set(v___f_276_, 1, v_entries_273_);
v___x_277_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_278_ = lean_array_size(v___x_275_);
v___x_279_ = ((size_t)0ULL);
v_entries_280_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_277_, v___x_275_, v___f_276_, v_sz_278_, v___x_279_, v___x_275_);
lean_dec(v___x_275_);
return v_entries_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg(lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_map_283_, lean_object* v_key_284_){
_start:
{
lean_object* v_entries_285_; lean_object* v_indexes_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_entry_289_; lean_object* v___x_290_; lean_object* v_snd_291_; 
v_entries_285_ = lean_ctor_get(v_map_283_, 0);
v_indexes_286_ = lean_ctor_get(v_map_283_, 1);
v___x_287_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_281_, v_inst_282_, v_indexes_286_, v_key_284_);
v___x_288_ = lean_unsigned_to_nat(0u);
v_entry_289_ = lean_array_fget(v___x_287_, v___x_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_array_fget_borrowed(v_entries_285_, v_entry_289_);
lean_dec(v_entry_289_);
v_snd_291_ = lean_ctor_get(v___x_290_, 1);
lean_inc(v_snd_291_);
return v_snd_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg___boxed(lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_map_294_, lean_object* v_key_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Internal_IndexMultiMap_get___redArg(v_inst_292_, v_inst_293_, v_map_294_, v_key_295_);
lean_dec_ref(v_map_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get(lean_object* v_00_u03b1_297_, lean_object* v_00_u03b2_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_map_301_, lean_object* v_key_302_, lean_object* v_h_303_){
_start:
{
lean_object* v_entries_304_; lean_object* v_indexes_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v_entry_308_; lean_object* v___x_309_; lean_object* v_snd_310_; 
v_entries_304_ = lean_ctor_get(v_map_301_, 0);
v_indexes_305_ = lean_ctor_get(v_map_301_, 1);
v___x_306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_299_, v_inst_300_, v_indexes_305_, v_key_302_);
v___x_307_ = lean_unsigned_to_nat(0u);
v_entry_308_ = lean_array_fget(v___x_306_, v___x_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_array_fget_borrowed(v_entries_304_, v_entry_308_);
lean_dec(v_entry_308_);
v_snd_310_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_snd_310_);
return v_snd_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___boxed(lean_object* v_00_u03b1_311_, lean_object* v_00_u03b2_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_map_315_, lean_object* v_key_316_, lean_object* v_h_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_Internal_IndexMultiMap_get(v_00_u03b1_311_, v_00_u03b2_312_, v_inst_313_, v_inst_314_, v_map_315_, v_key_316_, v_h_317_);
lean_dec_ref(v_map_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f___redArg(lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_map_321_, lean_object* v_key_322_){
_start:
{
uint8_t v___x_323_; 
lean_inc(v_key_322_);
lean_inc_ref(v_inst_320_);
lean_inc_ref(v_inst_319_);
v___x_323_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_319_, v_inst_320_, v_key_322_, v_map_321_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
lean_dec(v_key_322_);
lean_dec_ref(v_map_321_);
lean_dec_ref(v_inst_320_);
lean_dec_ref(v_inst_319_);
v___x_324_ = lean_box(0);
return v___x_324_;
}
else
{
lean_object* v_entries_325_; lean_object* v_indexes_326_; lean_object* v___x_327_; lean_object* v___f_328_; lean_object* v___x_329_; size_t v_sz_330_; size_t v___x_331_; lean_object* v_entries_332_; lean_object* v___x_333_; 
v_entries_325_ = lean_ctor_get(v_map_321_, 0);
lean_inc_ref(v_entries_325_);
v_indexes_326_ = lean_ctor_get(v_map_321_, 1);
lean_inc_ref(v_indexes_326_);
lean_dec_ref(v_map_321_);
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_319_, v_inst_320_, v_indexes_326_, v_key_322_);
lean_dec_ref(v_indexes_326_);
lean_inc_n(v___x_327_, 2);
v___f_328_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_328_, 0, v___x_327_);
lean_closure_set(v___f_328_, 1, v_entries_325_);
v___x_329_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_330_ = lean_array_size(v___x_327_);
v___x_331_ = ((size_t)0ULL);
v_entries_332_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_329_, v___x_327_, v___f_328_, v_sz_330_, v___x_331_, v___x_327_);
lean_dec(v___x_327_);
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v_entries_332_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f(lean_object* v_00_u03b1_334_, lean_object* v_00_u03b2_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_map_338_, lean_object* v_key_339_){
_start:
{
uint8_t v___x_340_; 
lean_inc(v_key_339_);
lean_inc_ref(v_inst_337_);
lean_inc_ref(v_inst_336_);
v___x_340_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_336_, v_inst_337_, v_key_339_, v_map_338_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec(v_key_339_);
lean_dec_ref(v_map_338_);
lean_dec_ref(v_inst_337_);
lean_dec_ref(v_inst_336_);
v___x_341_ = lean_box(0);
return v___x_341_;
}
else
{
lean_object* v_entries_342_; lean_object* v_indexes_343_; lean_object* v___x_344_; lean_object* v___f_345_; lean_object* v___x_346_; size_t v_sz_347_; size_t v___x_348_; lean_object* v_entries_349_; lean_object* v___x_350_; 
v_entries_342_ = lean_ctor_get(v_map_338_, 0);
lean_inc_ref(v_entries_342_);
v_indexes_343_ = lean_ctor_get(v_map_338_, 1);
lean_inc_ref(v_indexes_343_);
lean_dec_ref(v_map_338_);
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_336_, v_inst_337_, v_indexes_343_, v_key_339_);
lean_dec_ref(v_indexes_343_);
lean_inc_n(v___x_344_, 2);
v___f_345_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_345_, 0, v___x_344_);
lean_closure_set(v___f_345_, 1, v_entries_342_);
v___x_346_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_347_ = lean_array_size(v___x_344_);
v___x_348_ = ((size_t)0ULL);
v_entries_349_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_346_, v___x_344_, v___f_345_, v_sz_347_, v___x_348_, v___x_344_);
lean_dec(v___x_344_);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_entries_349_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg(lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_map_353_, lean_object* v_key_354_){
_start:
{
uint8_t v___x_355_; 
lean_inc(v_key_354_);
lean_inc_ref(v_inst_352_);
lean_inc_ref(v_inst_351_);
v___x_355_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_351_, v_inst_352_, v_key_354_, v_map_353_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec(v_key_354_);
lean_dec_ref(v_inst_352_);
lean_dec_ref(v_inst_351_);
v___x_356_ = lean_box(0);
return v___x_356_;
}
else
{
lean_object* v_entries_357_; lean_object* v_indexes_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_entry_361_; lean_object* v___x_362_; lean_object* v_snd_363_; lean_object* v___x_364_; 
v_entries_357_ = lean_ctor_get(v_map_353_, 0);
v_indexes_358_ = lean_ctor_get(v_map_353_, 1);
v___x_359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_351_, v_inst_352_, v_indexes_358_, v_key_354_);
v___x_360_ = lean_unsigned_to_nat(0u);
v_entry_361_ = lean_array_fget(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_array_fget_borrowed(v_entries_357_, v_entry_361_);
lean_dec(v_entry_361_);
v_snd_363_ = lean_ctor_get(v___x_362_, 1);
lean_inc(v_snd_363_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v_snd_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg___boxed(lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_map_367_, lean_object* v_key_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_Internal_IndexMultiMap_get_x3f___redArg(v_inst_365_, v_inst_366_, v_map_367_, v_key_368_);
lean_dec_ref(v_map_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_map_374_, lean_object* v_key_375_){
_start:
{
uint8_t v___x_376_; 
lean_inc(v_key_375_);
lean_inc_ref(v_inst_373_);
lean_inc_ref(v_inst_372_);
v___x_376_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_372_, v_inst_373_, v_key_375_, v_map_374_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec(v_key_375_);
lean_dec_ref(v_inst_373_);
lean_dec_ref(v_inst_372_);
v___x_377_ = lean_box(0);
return v___x_377_;
}
else
{
lean_object* v_entries_378_; lean_object* v_indexes_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v_entry_382_; lean_object* v___x_383_; lean_object* v_snd_384_; lean_object* v___x_385_; 
v_entries_378_ = lean_ctor_get(v_map_374_, 0);
v_indexes_379_ = lean_ctor_get(v_map_374_, 1);
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_372_, v_inst_373_, v_indexes_379_, v_key_375_);
v___x_381_ = lean_unsigned_to_nat(0u);
v_entry_382_ = lean_array_fget(v___x_380_, v___x_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_array_fget_borrowed(v_entries_378_, v_entry_382_);
lean_dec(v_entry_382_);
v_snd_384_ = lean_ctor_get(v___x_383_, 1);
lean_inc(v_snd_384_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v_snd_384_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___boxed(lean_object* v_00_u03b1_386_, lean_object* v_00_u03b2_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_map_390_, lean_object* v_key_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_Internal_IndexMultiMap_get_x3f(v_00_u03b1_386_, v_00_u03b2_387_, v_inst_388_, v_inst_389_, v_map_390_, v_key_391_);
lean_dec_ref(v_map_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(lean_object* v_inst_393_, lean_object* v_value_394_, lean_object* v___x_395_, lean_object* v___x_396_, lean_object* v_a_397_, lean_object* v_x_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_400_; uint8_t v___x_401_; 
lean_inc(v_a_397_);
v___x_400_ = lean_apply_2(v_inst_393_, v_a_397_, v_value_394_);
v___x_401_ = lean_unbox(v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec(v_a_397_);
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_395_);
return v___x_402_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec_ref(v___x_395_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v_a_397_);
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_396_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed(lean_object* v_inst_407_, lean_object* v_value_408_, lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v_a_411_, lean_object* v_x_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(v_inst_407_, v_value_408_, v___x_409_, v___x_410_, v_a_411_, v_x_412_, v___y_413_);
lean_dec_ref(v___y_413_);
return v_res_414_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry___redArg(lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_map_420_, lean_object* v_inst_421_, lean_object* v_key_422_, lean_object* v_value_423_){
_start:
{
uint8_t v___x_424_; 
lean_inc(v_key_422_);
lean_inc_ref(v_inst_419_);
lean_inc_ref(v_inst_418_);
v___x_424_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_418_, v_inst_419_, v_key_422_, v_map_420_);
if (v___x_424_ == 0)
{
lean_dec(v_value_423_);
lean_dec(v_key_422_);
lean_dec_ref(v_inst_421_);
lean_dec_ref(v_map_420_);
lean_dec_ref(v_inst_419_);
lean_dec_ref(v_inst_418_);
return v___x_424_;
}
else
{
lean_object* v_entries_425_; lean_object* v_indexes_426_; lean_object* v___x_427_; lean_object* v___f_428_; lean_object* v___x_429_; size_t v_sz_430_; size_t v___x_431_; lean_object* v_entries_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___f_435_; size_t v_sz_436_; lean_object* v___x_437_; lean_object* v_fst_438_; 
v_entries_425_ = lean_ctor_get(v_map_420_, 0);
lean_inc_ref(v_entries_425_);
v_indexes_426_ = lean_ctor_get(v_map_420_, 1);
lean_inc_ref(v_indexes_426_);
lean_dec_ref(v_map_420_);
v___x_427_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_418_, v_inst_419_, v_indexes_426_, v_key_422_);
lean_dec_ref(v_indexes_426_);
lean_inc_n(v___x_427_, 2);
v___f_428_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_428_, 0, v___x_427_);
lean_closure_set(v___f_428_, 1, v_entries_425_);
v___x_429_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_430_ = lean_array_size(v___x_427_);
v___x_431_ = ((size_t)0ULL);
v_entries_432_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_429_, v___x_427_, v___f_428_, v_sz_430_, v___x_431_, v___x_427_);
lean_dec(v___x_427_);
v___x_433_ = lean_box(0);
v___x_434_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_435_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_435_, 0, v_inst_421_);
lean_closure_set(v___f_435_, 1, v_value_423_);
lean_closure_set(v___f_435_, 2, v___x_434_);
lean_closure_set(v___f_435_, 3, v___x_433_);
v_sz_436_ = lean_array_size(v_entries_432_);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_429_, v_entries_432_, v___f_435_, v_sz_436_, v___x_431_, v___x_434_);
v_fst_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_fst_438_);
lean_dec(v___x_437_);
if (lean_obj_tag(v_fst_438_) == 0)
{
uint8_t v___x_439_; 
v___x_439_ = 0;
return v___x_439_;
}
else
{
lean_object* v_val_440_; 
v_val_440_ = lean_ctor_get(v_fst_438_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v_fst_438_, 1);
if (lean_obj_tag(v_val_440_) == 0)
{
uint8_t v___x_441_; 
v___x_441_ = 0;
return v___x_441_;
}
else
{
lean_dec_ref_known(v_val_440_, 1);
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___boxed(lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_map_444_, lean_object* v_inst_445_, lean_object* v_key_446_, lean_object* v_value_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg(v_inst_442_, v_inst_443_, v_map_444_, v_inst_445_, v_key_446_, v_value_447_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry(lean_object* v_00_u03b1_450_, lean_object* v_00_u03b2_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_map_454_, lean_object* v_inst_455_, lean_object* v_key_456_, lean_object* v_value_457_){
_start:
{
uint8_t v___x_458_; 
lean_inc(v_key_456_);
lean_inc_ref(v_inst_453_);
lean_inc_ref(v_inst_452_);
v___x_458_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_452_, v_inst_453_, v_key_456_, v_map_454_);
if (v___x_458_ == 0)
{
lean_dec(v_value_457_);
lean_dec(v_key_456_);
lean_dec_ref(v_inst_455_);
lean_dec_ref(v_map_454_);
lean_dec_ref(v_inst_453_);
lean_dec_ref(v_inst_452_);
return v___x_458_;
}
else
{
lean_object* v_entries_459_; lean_object* v_indexes_460_; lean_object* v___x_461_; lean_object* v___f_462_; lean_object* v___x_463_; size_t v_sz_464_; size_t v___x_465_; lean_object* v_entries_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___f_469_; size_t v_sz_470_; lean_object* v___x_471_; lean_object* v_fst_472_; 
v_entries_459_ = lean_ctor_get(v_map_454_, 0);
lean_inc_ref(v_entries_459_);
v_indexes_460_ = lean_ctor_get(v_map_454_, 1);
lean_inc_ref(v_indexes_460_);
lean_dec_ref(v_map_454_);
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_452_, v_inst_453_, v_indexes_460_, v_key_456_);
lean_dec_ref(v_indexes_460_);
lean_inc_n(v___x_461_, 2);
v___f_462_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_462_, 0, v___x_461_);
lean_closure_set(v___f_462_, 1, v_entries_459_);
v___x_463_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_464_ = lean_array_size(v___x_461_);
v___x_465_ = ((size_t)0ULL);
v_entries_466_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_463_, v___x_461_, v___f_462_, v_sz_464_, v___x_465_, v___x_461_);
lean_dec(v___x_461_);
v___x_467_ = lean_box(0);
v___x_468_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_469_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_469_, 0, v_inst_455_);
lean_closure_set(v___f_469_, 1, v_value_457_);
lean_closure_set(v___f_469_, 2, v___x_468_);
lean_closure_set(v___f_469_, 3, v___x_467_);
v_sz_470_ = lean_array_size(v_entries_466_);
v___x_471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_463_, v_entries_466_, v___f_469_, v_sz_470_, v___x_465_, v___x_468_);
v_fst_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_fst_472_);
lean_dec(v___x_471_);
if (lean_obj_tag(v_fst_472_) == 0)
{
uint8_t v___x_473_; 
v___x_473_ = 0;
return v___x_473_;
}
else
{
lean_object* v_val_474_; 
v_val_474_ = lean_ctor_get(v_fst_472_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v_fst_472_, 1);
if (lean_obj_tag(v_val_474_) == 0)
{
uint8_t v___x_475_; 
v___x_475_ = 0;
return v___x_475_;
}
else
{
lean_dec_ref_known(v_val_474_, 1);
return v___x_458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___boxed(lean_object* v_00_u03b1_476_, lean_object* v_00_u03b2_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_map_480_, lean_object* v_inst_481_, lean_object* v_key_482_, lean_object* v_value_483_){
_start:
{
uint8_t v_res_484_; lean_object* v_r_485_; 
v_res_484_ = l_Std_Internal_IndexMultiMap_hasEntry(v_00_u03b1_476_, v_00_u03b2_477_, v_inst_478_, v_inst_479_, v_map_480_, v_inst_481_, v_key_482_, v_value_483_);
v_r_485_ = lean_box(v_res_484_);
return v_r_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f___redArg(lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_map_488_, lean_object* v_key_489_){
_start:
{
uint8_t v___x_490_; 
lean_inc(v_key_489_);
lean_inc_ref(v_inst_487_);
lean_inc_ref(v_inst_486_);
v___x_490_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_486_, v_inst_487_, v_key_489_, v_map_488_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_dec(v_key_489_);
lean_dec_ref(v_map_488_);
lean_dec_ref(v_inst_487_);
lean_dec_ref(v_inst_486_);
v___x_491_ = lean_box(0);
return v___x_491_;
}
else
{
lean_object* v_entries_492_; lean_object* v_indexes_493_; lean_object* v___x_494_; lean_object* v___f_495_; lean_object* v___x_496_; size_t v_sz_497_; size_t v___x_498_; lean_object* v_entries_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_entries_492_ = lean_ctor_get(v_map_488_, 0);
lean_inc_ref(v_entries_492_);
v_indexes_493_ = lean_ctor_get(v_map_488_, 1);
lean_inc_ref(v_indexes_493_);
lean_dec_ref(v_map_488_);
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_486_, v_inst_487_, v_indexes_493_, v_key_489_);
lean_dec_ref(v_indexes_493_);
lean_inc_n(v___x_494_, 2);
v___f_495_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_495_, 0, v___x_494_);
lean_closure_set(v___f_495_, 1, v_entries_492_);
v___x_496_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_497_ = lean_array_size(v___x_494_);
v___x_498_ = ((size_t)0ULL);
v_entries_499_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_496_, v___x_494_, v___f_495_, v_sz_497_, v___x_498_, v___x_494_);
lean_dec(v___x_494_);
v___x_500_ = lean_array_get_size(v_entries_499_);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_sub(v___x_500_, v___x_501_);
v___x_503_ = lean_nat_dec_lt(v___x_502_, v___x_500_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec(v___x_502_);
lean_dec(v_entries_499_);
v___x_504_ = lean_box(0);
return v___x_504_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_array_fget(v_entries_499_, v___x_502_);
lean_dec(v___x_502_);
lean_dec(v_entries_499_);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f(lean_object* v_00_u03b1_507_, lean_object* v_00_u03b2_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_map_511_, lean_object* v_key_512_){
_start:
{
uint8_t v___x_513_; 
lean_inc(v_key_512_);
lean_inc_ref(v_inst_510_);
lean_inc_ref(v_inst_509_);
v___x_513_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_509_, v_inst_510_, v_key_512_, v_map_511_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_dec(v_key_512_);
lean_dec_ref(v_map_511_);
lean_dec_ref(v_inst_510_);
lean_dec_ref(v_inst_509_);
v___x_514_ = lean_box(0);
return v___x_514_;
}
else
{
lean_object* v_entries_515_; lean_object* v_indexes_516_; lean_object* v___x_517_; lean_object* v___f_518_; lean_object* v___x_519_; size_t v_sz_520_; size_t v___x_521_; lean_object* v_entries_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_entries_515_ = lean_ctor_get(v_map_511_, 0);
lean_inc_ref(v_entries_515_);
v_indexes_516_ = lean_ctor_get(v_map_511_, 1);
lean_inc_ref(v_indexes_516_);
lean_dec_ref(v_map_511_);
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_509_, v_inst_510_, v_indexes_516_, v_key_512_);
lean_dec_ref(v_indexes_516_);
lean_inc_n(v___x_517_, 2);
v___f_518_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_518_, 0, v___x_517_);
lean_closure_set(v___f_518_, 1, v_entries_515_);
v___x_519_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_520_ = lean_array_size(v___x_517_);
v___x_521_ = ((size_t)0ULL);
v_entries_522_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_519_, v___x_517_, v___f_518_, v_sz_520_, v___x_521_, v___x_517_);
lean_dec(v___x_517_);
v___x_523_ = lean_array_get_size(v_entries_522_);
v___x_524_ = lean_unsigned_to_nat(1u);
v___x_525_ = lean_nat_sub(v___x_523_, v___x_524_);
v___x_526_ = lean_nat_dec_lt(v___x_525_, v___x_523_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
lean_dec(v___x_525_);
lean_dec(v_entries_522_);
v___x_527_ = lean_box(0);
return v___x_527_;
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_array_fget(v_entries_522_, v___x_525_);
lean_dec(v___x_525_);
lean_dec(v_entries_522_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg(lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_map_532_, lean_object* v_key_533_, lean_object* v_d_534_){
_start:
{
uint8_t v___x_535_; 
lean_inc(v_key_533_);
lean_inc_ref(v_inst_531_);
lean_inc_ref(v_inst_530_);
v___x_535_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_530_, v_inst_531_, v_key_533_, v_map_532_);
if (v___x_535_ == 0)
{
lean_dec(v_key_533_);
lean_dec_ref(v_inst_531_);
lean_dec_ref(v_inst_530_);
lean_inc(v_d_534_);
return v_d_534_;
}
else
{
lean_object* v_entries_536_; lean_object* v_indexes_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_entry_540_; lean_object* v___x_541_; lean_object* v_snd_542_; 
v_entries_536_ = lean_ctor_get(v_map_532_, 0);
v_indexes_537_ = lean_ctor_get(v_map_532_, 1);
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_530_, v_inst_531_, v_indexes_537_, v_key_533_);
v___x_539_ = lean_unsigned_to_nat(0u);
v_entry_540_ = lean_array_fget(v___x_538_, v___x_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_array_fget_borrowed(v_entries_536_, v_entry_540_);
lean_dec(v_entry_540_);
v_snd_542_ = lean_ctor_get(v___x_541_, 1);
lean_inc(v_snd_542_);
return v_snd_542_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg___boxed(lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_map_545_, lean_object* v_key_546_, lean_object* v_d_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Internal_IndexMultiMap_getD___redArg(v_inst_543_, v_inst_544_, v_map_545_, v_key_546_, v_d_547_);
lean_dec(v_d_547_);
lean_dec_ref(v_map_545_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD(lean_object* v_00_u03b1_549_, lean_object* v_00_u03b2_550_, lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_map_553_, lean_object* v_key_554_, lean_object* v_d_555_){
_start:
{
uint8_t v___x_556_; 
lean_inc(v_key_554_);
lean_inc_ref(v_inst_552_);
lean_inc_ref(v_inst_551_);
v___x_556_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_551_, v_inst_552_, v_key_554_, v_map_553_);
if (v___x_556_ == 0)
{
lean_dec(v_key_554_);
lean_dec_ref(v_inst_552_);
lean_dec_ref(v_inst_551_);
lean_inc(v_d_555_);
return v_d_555_;
}
else
{
lean_object* v_entries_557_; lean_object* v_indexes_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_entry_561_; lean_object* v___x_562_; lean_object* v_snd_563_; 
v_entries_557_ = lean_ctor_get(v_map_553_, 0);
v_indexes_558_ = lean_ctor_get(v_map_553_, 1);
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_551_, v_inst_552_, v_indexes_558_, v_key_554_);
v___x_560_ = lean_unsigned_to_nat(0u);
v_entry_561_ = lean_array_fget(v___x_559_, v___x_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_array_fget_borrowed(v_entries_557_, v_entry_561_);
lean_dec(v_entry_561_);
v_snd_563_ = lean_ctor_get(v___x_562_, 1);
lean_inc(v_snd_563_);
return v_snd_563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___boxed(lean_object* v_00_u03b1_564_, lean_object* v_00_u03b2_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_map_568_, lean_object* v_key_569_, lean_object* v_d_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Std_Internal_IndexMultiMap_getD(v_00_u03b1_564_, v_00_u03b2_565_, v_inst_566_, v_inst_567_, v_map_568_, v_key_569_, v_d_570_);
lean_dec(v_d_570_);
lean_dec_ref(v_map_568_);
return v_res_571_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_575_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2));
v___x_576_ = lean_unsigned_to_nat(14u);
v___x_577_ = lean_unsigned_to_nat(22u);
v___x_578_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1));
v___x_579_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0));
v___x_580_ = l_mkPanicMessageWithDecl(v___x_579_, v___x_578_, v___x_577_, v___x_576_, v___x_575_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg(lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_map_584_, lean_object* v_key_585_){
_start:
{
uint8_t v___x_586_; 
lean_inc(v_key_585_);
lean_inc_ref(v_inst_582_);
lean_inc_ref(v_inst_581_);
v___x_586_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_581_, v_inst_582_, v_key_585_, v_map_584_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_key_585_);
lean_dec_ref(v_inst_582_);
lean_dec_ref(v_inst_581_);
v___x_587_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_588_ = l_panic___redArg(v_inst_583_, v___x_587_);
return v___x_588_;
}
else
{
lean_object* v_entries_589_; lean_object* v_indexes_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_entry_593_; lean_object* v___x_594_; lean_object* v_snd_595_; 
v_entries_589_ = lean_ctor_get(v_map_584_, 0);
v_indexes_590_ = lean_ctor_get(v_map_584_, 1);
v___x_591_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_581_, v_inst_582_, v_indexes_590_, v_key_585_);
v___x_592_ = lean_unsigned_to_nat(0u);
v_entry_593_ = lean_array_fget(v___x_591_, v___x_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_array_fget_borrowed(v_entries_589_, v_entry_593_);
lean_dec(v_entry_593_);
v_snd_595_ = lean_ctor_get(v___x_594_, 1);
lean_inc(v_snd_595_);
return v_snd_595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___boxed(lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_map_599_, lean_object* v_key_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_Internal_IndexMultiMap_get_x21___redArg(v_inst_596_, v_inst_597_, v_inst_598_, v_map_599_, v_key_600_);
lean_dec_ref(v_map_599_);
lean_dec(v_inst_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21(lean_object* v_00_u03b1_602_, lean_object* v_00_u03b2_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_map_607_, lean_object* v_key_608_){
_start:
{
uint8_t v___x_609_; 
lean_inc(v_key_608_);
lean_inc_ref(v_inst_605_);
lean_inc_ref(v_inst_604_);
v___x_609_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_604_, v_inst_605_, v_key_608_, v_map_607_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v_key_608_);
lean_dec_ref(v_inst_605_);
lean_dec_ref(v_inst_604_);
v___x_610_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_611_ = l_panic___redArg(v_inst_606_, v___x_610_);
return v___x_611_;
}
else
{
lean_object* v_entries_612_; lean_object* v_indexes_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_entry_616_; lean_object* v___x_617_; lean_object* v_snd_618_; 
v_entries_612_ = lean_ctor_get(v_map_607_, 0);
v_indexes_613_ = lean_ctor_get(v_map_607_, 1);
v___x_614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_604_, v_inst_605_, v_indexes_613_, v_key_608_);
v___x_615_ = lean_unsigned_to_nat(0u);
v_entry_616_ = lean_array_fget(v___x_614_, v___x_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_array_fget_borrowed(v_entries_612_, v_entry_616_);
lean_dec(v_entry_616_);
v_snd_618_ = lean_ctor_get(v___x_617_, 1);
lean_inc(v_snd_618_);
return v_snd_618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___boxed(lean_object* v_00_u03b1_619_, lean_object* v_00_u03b2_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_map_624_, lean_object* v_key_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Internal_IndexMultiMap_get_x21(v_00_u03b1_619_, v_00_u03b2_620_, v_inst_621_, v_inst_622_, v_inst_623_, v_map_624_, v_key_625_);
lean_dec_ref(v_map_624_);
lean_dec(v_inst_623_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(lean_object* v_i_627_, lean_object* v_x_628_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_mk_empty_array_with_capacity(v___x_629_);
v___x_631_ = lean_array_push(v___x_630_, v_i_627_);
v___x_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
else
{
lean_object* v_val_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_641_; 
v_val_633_ = lean_ctor_get(v_x_628_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_628_);
if (v_isSharedCheck_641_ == 0)
{
v___x_635_ = v_x_628_;
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_val_633_);
lean_dec(v_x_628_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = lean_array_push(v_val_633_, v_i_627_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_637_);
v___x_639_ = v___x_635_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg(lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_map_644_, lean_object* v_key_645_, lean_object* v_value_646_){
_start:
{
lean_object* v_entries_647_; lean_object* v_indexes_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_660_; 
v_entries_647_ = lean_ctor_get(v_map_644_, 0);
v_indexes_648_ = lean_ctor_get(v_map_644_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v_map_644_);
if (v_isSharedCheck_660_ == 0)
{
v___x_650_ = v_map_644_;
v_isShared_651_ = v_isSharedCheck_660_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_indexes_648_);
lean_inc(v_entries_647_);
lean_dec(v_map_644_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_660_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v_i_652_; lean_object* v_f_653_; lean_object* v___x_654_; lean_object* v_entries_655_; lean_object* v_indexes_656_; lean_object* v___x_658_; 
v_i_652_ = lean_array_get_size(v_entries_647_);
v_f_653_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_653_, 0, v_i_652_);
lean_inc(v_key_645_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v_key_645_);
lean_ctor_set(v___x_654_, 1, v_value_646_);
v_entries_655_ = lean_array_push(v_entries_647_, v___x_654_);
v_indexes_656_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_642_, v_inst_643_, v_indexes_648_, v_key_645_, v_f_653_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v_indexes_656_);
lean_ctor_set(v___x_650_, 0, v_entries_655_);
v___x_658_ = v___x_650_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_entries_655_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_indexes_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_map_667_, lean_object* v_key_668_, lean_object* v_value_669_){
_start:
{
lean_object* v_entries_670_; lean_object* v_indexes_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_683_; 
v_entries_670_ = lean_ctor_get(v_map_667_, 0);
v_indexes_671_ = lean_ctor_get(v_map_667_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_map_667_);
if (v_isSharedCheck_683_ == 0)
{
v___x_673_ = v_map_667_;
v_isShared_674_ = v_isSharedCheck_683_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_indexes_671_);
lean_inc(v_entries_670_);
lean_dec(v_map_667_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_683_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_i_675_; lean_object* v_f_676_; lean_object* v___x_677_; lean_object* v_entries_678_; lean_object* v_indexes_679_; lean_object* v___x_681_; 
v_i_675_ = lean_array_get_size(v_entries_670_);
v_f_676_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_676_, 0, v_i_675_);
lean_inc(v_key_668_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_key_668_);
lean_ctor_set(v___x_677_, 1, v_value_669_);
v_entries_678_ = lean_array_push(v_entries_670_, v___x_677_);
v_indexes_679_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_663_, v_inst_664_, v_indexes_671_, v_key_668_, v_f_676_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v_indexes_679_);
lean_ctor_set(v___x_673_, 0, v_entries_678_);
v___x_681_ = v___x_673_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_entries_678_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_indexes_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1(lean_object* v_key_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_x1_687_, lean_object* v_x2_688_){
_start:
{
lean_object* v_entries_689_; lean_object* v_indexes_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_702_; 
v_entries_689_ = lean_ctor_get(v_x1_687_, 0);
v_indexes_690_ = lean_ctor_get(v_x1_687_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_x1_687_);
if (v_isSharedCheck_702_ == 0)
{
v___x_692_ = v_x1_687_;
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_indexes_690_);
lean_inc(v_entries_689_);
lean_dec(v_x1_687_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_i_694_; lean_object* v_f_695_; lean_object* v___x_696_; lean_object* v_entries_697_; lean_object* v_indexes_698_; lean_object* v___x_700_; 
v_i_694_ = lean_array_get_size(v_entries_689_);
v_f_695_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_695_, 0, v_i_694_);
lean_inc(v_key_684_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_key_684_);
lean_ctor_set(v___x_696_, 1, v_x2_688_);
v_entries_697_ = lean_array_push(v_entries_689_, v___x_696_);
v_indexes_698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_685_, v_inst_686_, v_indexes_690_, v_key_684_, v_f_695_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v_indexes_698_);
lean_ctor_set(v___x_692_, 0, v_entries_697_);
v___x_700_ = v___x_692_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_entries_697_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_indexes_698_);
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
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg(lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_map_705_, lean_object* v_key_706_, lean_object* v_values_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_array_get_size(v_values_707_);
v___x_710_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_711_ = lean_nat_dec_lt(v___x_708_, v___x_709_);
if (v___x_711_ == 0)
{
lean_dec_ref(v_values_707_);
lean_dec(v_key_706_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
return v_map_705_;
}
else
{
lean_object* v___f_712_; uint8_t v___x_713_; 
v___f_712_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_712_, 0, v_key_706_);
lean_closure_set(v___f_712_, 1, v_inst_703_);
lean_closure_set(v___f_712_, 2, v_inst_704_);
v___x_713_ = lean_nat_dec_le(v___x_709_, v___x_709_);
if (v___x_713_ == 0)
{
if (v___x_711_ == 0)
{
lean_dec_ref(v___f_712_);
lean_dec_ref(v_values_707_);
return v_map_705_;
}
else
{
size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v___x_714_ = ((size_t)0ULL);
v___x_715_ = lean_usize_of_nat(v___x_709_);
v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_710_, v___f_712_, v_values_707_, v___x_714_, v___x_715_, v_map_705_);
return v___x_716_;
}
}
else
{
size_t v___x_717_; size_t v___x_718_; lean_object* v___x_719_; 
v___x_717_ = ((size_t)0ULL);
v___x_718_ = lean_usize_of_nat(v___x_709_);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_710_, v___f_712_, v_values_707_, v___x_717_, v___x_718_, v_map_705_);
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany(lean_object* v_00_u03b1_720_, lean_object* v_00_u03b2_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_map_726_, lean_object* v_key_727_, lean_object* v_values_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = lean_array_get_size(v_values_728_);
v___x_731_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_732_ = lean_nat_dec_lt(v___x_729_, v___x_730_);
if (v___x_732_ == 0)
{
lean_dec_ref(v_values_728_);
lean_dec(v_key_727_);
lean_dec_ref(v_inst_723_);
lean_dec_ref(v_inst_722_);
return v_map_726_;
}
else
{
lean_object* v___f_733_; uint8_t v___x_734_; 
v___f_733_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_733_, 0, v_key_727_);
lean_closure_set(v___f_733_, 1, v_inst_722_);
lean_closure_set(v___f_733_, 2, v_inst_723_);
v___x_734_ = lean_nat_dec_le(v___x_730_, v___x_730_);
if (v___x_734_ == 0)
{
if (v___x_732_ == 0)
{
lean_dec_ref(v___f_733_);
lean_dec_ref(v_values_728_);
return v_map_726_;
}
else
{
size_t v___x_735_; size_t v___x_736_; lean_object* v___x_737_; 
v___x_735_ = ((size_t)0ULL);
v___x_736_ = lean_usize_of_nat(v___x_730_);
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_731_, v___f_733_, v_values_728_, v___x_735_, v___x_736_, v_map_726_);
return v___x_737_;
}
}
else
{
size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; 
v___x_738_ = ((size_t)0ULL);
v___x_739_ = lean_usize_of_nat(v___x_730_);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_731_, v___f_733_, v_values_728_, v___x_738_, v___x_739_, v_map_726_);
return v___x_740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object* v_00_u03b1_741_, lean_object* v_00_u03b2_742_, lean_object* v_inst_743_, lean_object* v_inst_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___boxed(lean_object* v_00_u03b1_746_, lean_object* v_00_u03b2_747_, lean_object* v_inst_748_, lean_object* v_inst_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_Internal_IndexMultiMap_empty(v_00_u03b1_746_, v_00_u03b2_747_, v_inst_748_, v_inst_749_);
lean_dec_ref(v_inst_749_);
lean_dec_ref(v_inst_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1(lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_acc_753_, lean_object* v_x_754_){
_start:
{
lean_object* v_fst_755_; lean_object* v_entries_756_; lean_object* v_indexes_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_768_; 
v_fst_755_ = lean_ctor_get(v_x_754_, 0);
lean_inc(v_fst_755_);
v_entries_756_ = lean_ctor_get(v_acc_753_, 0);
v_indexes_757_ = lean_ctor_get(v_acc_753_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_acc_753_);
if (v_isSharedCheck_768_ == 0)
{
v___x_759_ = v_acc_753_;
v_isShared_760_ = v_isSharedCheck_768_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_indexes_757_);
lean_inc(v_entries_756_);
lean_dec(v_acc_753_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_768_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_i_761_; lean_object* v_f_762_; lean_object* v_entries_763_; lean_object* v_indexes_764_; lean_object* v___x_766_; 
v_i_761_ = lean_array_get_size(v_entries_756_);
v_f_762_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_762_, 0, v_i_761_);
v_entries_763_ = lean_array_push(v_entries_756_, v_x_754_);
v_indexes_764_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_751_, v_inst_752_, v_indexes_757_, v_fst_755_, v_f_762_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v_indexes_764_);
lean_ctor_set(v___x_759_, 0, v_entries_763_);
v___x_766_ = v___x_759_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_entries_763_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_indexes_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg(lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_pairs_771_){
_start:
{
lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
lean_inc_ref(v_inst_770_);
lean_inc_ref(v_inst_769_);
v___f_772_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_772_, 0, v_inst_769_);
lean_closure_set(v___f_772_, 1, v_inst_770_);
v___x_773_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_769_, v_inst_770_);
lean_dec_ref(v_inst_770_);
lean_dec_ref(v_inst_769_);
v___x_774_ = l_List_foldl___redArg(v___f_772_, v___x_773_, v_pairs_771_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList(lean_object* v_00_u03b1_775_, lean_object* v_00_u03b2_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_pairs_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Std_Internal_IndexMultiMap_ofList___redArg(v_inst_777_, v_inst_778_, v_pairs_781_);
return v___x_782_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains___redArg(lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_map_785_, lean_object* v_key_786_){
_start:
{
lean_object* v_indexes_787_; uint8_t v___x_788_; 
v_indexes_787_ = lean_ctor_get(v_map_785_, 1);
v___x_788_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_783_, v_inst_784_, v_indexes_787_, v_key_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___redArg___boxed(lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_map_791_, lean_object* v_key_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l_Std_Internal_IndexMultiMap_contains___redArg(v_inst_789_, v_inst_790_, v_map_791_, v_key_792_);
lean_dec_ref(v_map_791_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains(lean_object* v_00_u03b1_795_, lean_object* v_00_u03b2_796_, lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_map_799_, lean_object* v_key_800_){
_start:
{
lean_object* v_indexes_801_; uint8_t v___x_802_; 
v_indexes_801_ = lean_ctor_get(v_map_799_, 1);
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_797_, v_inst_798_, v_indexes_801_, v_key_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___boxed(lean_object* v_00_u03b1_803_, lean_object* v_00_u03b2_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_map_807_, lean_object* v_key_808_){
_start:
{
uint8_t v_res_809_; lean_object* v_r_810_; 
v_res_809_ = l_Std_Internal_IndexMultiMap_contains(v_00_u03b1_803_, v_00_u03b2_804_, v_inst_805_, v_inst_806_, v_map_807_, v_key_808_);
lean_dec_ref(v_map_807_);
v_r_810_ = lean_box(v_res_809_);
return v_r_810_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg___lam__1(lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_key_813_, lean_object* v_f_814_, lean_object* v_x1_815_, lean_object* v_x2_816_){
_start:
{
lean_object* v_fst_817_; lean_object* v_snd_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_843_; 
v_fst_817_ = lean_ctor_get(v_x2_816_, 0);
v_snd_818_ = lean_ctor_get(v_x2_816_, 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v_x2_816_);
if (v_isSharedCheck_843_ == 0)
{
v___x_820_ = v_x2_816_;
v_isShared_821_ = v_isSharedCheck_843_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_snd_818_);
lean_inc(v_fst_817_);
lean_dec(v_x2_816_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_843_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___y_823_; lean_object* v___x_840_; uint8_t v___x_841_; 
lean_inc_ref(v_inst_811_);
lean_inc(v_fst_817_);
v___x_840_ = lean_apply_2(v_inst_811_, v_fst_817_, v_key_813_);
v___x_841_ = lean_unbox(v___x_840_);
if (v___x_841_ == 0)
{
lean_dec(v_f_814_);
v___y_823_ = v_snd_818_;
goto v___jp_822_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = lean_apply_1(v_f_814_, v_snd_818_);
v___y_823_ = v___x_842_;
goto v___jp_822_;
}
v___jp_822_:
{
lean_object* v_entries_824_; lean_object* v_indexes_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_839_; 
v_entries_824_ = lean_ctor_get(v_x1_815_, 0);
v_indexes_825_ = lean_ctor_get(v_x1_815_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_x1_815_);
if (v_isSharedCheck_839_ == 0)
{
v___x_827_ = v_x1_815_;
v_isShared_828_ = v_isSharedCheck_839_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_indexes_825_);
lean_inc(v_entries_824_);
lean_dec(v_x1_815_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_839_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_i_829_; lean_object* v_f_830_; lean_object* v___x_832_; 
v_i_829_ = lean_array_get_size(v_entries_824_);
v_f_830_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_830_, 0, v_i_829_);
lean_inc(v_fst_817_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___y_823_);
v___x_832_ = v___x_820_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_fst_817_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___y_823_);
v___x_832_ = v_reuseFailAlloc_838_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v_entries_833_; lean_object* v_indexes_834_; lean_object* v___x_836_; 
v_entries_833_ = lean_array_push(v_entries_824_, v___x_832_);
v_indexes_834_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_811_, v_inst_812_, v_indexes_825_, v_fst_817_, v_f_830_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 1, v_indexes_834_);
lean_ctor_set(v___x_827_, 0, v_entries_833_);
v___x_836_ = v___x_827_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_entries_833_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_indexes_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg(lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_map_846_, lean_object* v_key_847_, lean_object* v_f_848_){
_start:
{
uint8_t v___x_849_; 
lean_inc(v_key_847_);
lean_inc_ref(v_inst_845_);
lean_inc_ref(v_inst_844_);
v___x_849_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_844_, v_inst_845_, v_key_847_, v_map_846_);
if (v___x_849_ == 0)
{
lean_dec(v_f_848_);
lean_dec(v_key_847_);
lean_dec_ref(v_inst_845_);
lean_dec_ref(v_inst_844_);
return v_map_846_;
}
else
{
lean_object* v_entries_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v_entries_850_ = lean_ctor_get(v_map_846_, 0);
lean_inc_ref(v_entries_850_);
lean_dec_ref(v_map_846_);
v___x_851_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_844_, v_inst_845_);
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = lean_array_get_size(v_entries_850_);
v___x_854_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_855_ = lean_nat_dec_lt(v___x_852_, v___x_853_);
if (v___x_855_ == 0)
{
lean_dec_ref(v_entries_850_);
lean_dec(v_f_848_);
lean_dec(v_key_847_);
lean_dec_ref(v_inst_845_);
lean_dec_ref(v_inst_844_);
return v___x_851_;
}
else
{
lean_object* v___f_856_; uint8_t v___x_857_; 
v___f_856_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_856_, 0, v_inst_844_);
lean_closure_set(v___f_856_, 1, v_inst_845_);
lean_closure_set(v___f_856_, 2, v_key_847_);
lean_closure_set(v___f_856_, 3, v_f_848_);
v___x_857_ = lean_nat_dec_le(v___x_853_, v___x_853_);
if (v___x_857_ == 0)
{
if (v___x_855_ == 0)
{
lean_dec_ref(v___f_856_);
lean_dec_ref(v_entries_850_);
return v___x_851_;
}
else
{
size_t v___x_858_; size_t v___x_859_; lean_object* v___x_860_; 
v___x_858_ = ((size_t)0ULL);
v___x_859_ = lean_usize_of_nat(v___x_853_);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_854_, v___f_856_, v_entries_850_, v___x_858_, v___x_859_, v___x_851_);
return v___x_860_;
}
}
else
{
size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; 
v___x_861_ = ((size_t)0ULL);
v___x_862_ = lean_usize_of_nat(v___x_853_);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_854_, v___f_856_, v_entries_850_, v___x_861_, v___x_862_, v___x_851_);
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update(lean_object* v_00_u03b1_864_, lean_object* v_00_u03b2_865_, lean_object* v_inst_866_, lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_inst_869_, lean_object* v_map_870_, lean_object* v_key_871_, lean_object* v_f_872_){
_start:
{
uint8_t v___x_873_; 
lean_inc(v_key_871_);
lean_inc_ref(v_inst_867_);
lean_inc_ref(v_inst_866_);
v___x_873_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_866_, v_inst_867_, v_key_871_, v_map_870_);
if (v___x_873_ == 0)
{
lean_dec(v_f_872_);
lean_dec(v_key_871_);
lean_dec_ref(v_inst_867_);
lean_dec_ref(v_inst_866_);
return v_map_870_;
}
else
{
lean_object* v_entries_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v_entries_874_ = lean_ctor_get(v_map_870_, 0);
lean_inc_ref(v_entries_874_);
lean_dec_ref(v_map_870_);
v___x_875_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_866_, v_inst_867_);
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = lean_array_get_size(v_entries_874_);
v___x_878_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_879_ = lean_nat_dec_lt(v___x_876_, v___x_877_);
if (v___x_879_ == 0)
{
lean_dec_ref(v_entries_874_);
lean_dec(v_f_872_);
lean_dec(v_key_871_);
lean_dec_ref(v_inst_867_);
lean_dec_ref(v_inst_866_);
return v___x_875_;
}
else
{
lean_object* v___f_880_; uint8_t v___x_881_; 
v___f_880_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_880_, 0, v_inst_866_);
lean_closure_set(v___f_880_, 1, v_inst_867_);
lean_closure_set(v___f_880_, 2, v_key_871_);
lean_closure_set(v___f_880_, 3, v_f_872_);
v___x_881_ = lean_nat_dec_le(v___x_877_, v___x_877_);
if (v___x_881_ == 0)
{
if (v___x_879_ == 0)
{
lean_dec_ref(v___f_880_);
lean_dec_ref(v_entries_874_);
return v___x_875_;
}
else
{
size_t v___x_882_; size_t v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((size_t)0ULL);
v___x_883_ = lean_usize_of_nat(v___x_877_);
v___x_884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_878_, v___f_880_, v_entries_874_, v___x_882_, v___x_883_, v___x_875_);
return v___x_884_;
}
}
else
{
size_t v___x_885_; size_t v___x_886_; lean_object* v___x_887_; 
v___x_885_ = ((size_t)0ULL);
v___x_886_ = lean_usize_of_nat(v___x_877_);
v___x_887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_878_, v___f_880_, v_entries_874_, v___x_885_, v___x_886_, v___x_875_);
return v___x_887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast___redArg(lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_map_890_, lean_object* v_key_891_, lean_object* v_value_892_){
_start:
{
uint8_t v___x_893_; 
lean_inc(v_key_891_);
lean_inc_ref(v_inst_889_);
lean_inc_ref(v_inst_888_);
v___x_893_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_888_, v_inst_889_, v_key_891_, v_map_890_);
if (v___x_893_ == 0)
{
lean_dec(v_value_892_);
lean_dec(v_key_891_);
lean_dec_ref(v_inst_889_);
lean_dec_ref(v_inst_888_);
return v_map_890_;
}
else
{
lean_object* v_entries_894_; lean_object* v_indexes_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_909_; 
v_entries_894_ = lean_ctor_get(v_map_890_, 0);
v_indexes_895_ = lean_ctor_get(v_map_890_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_map_890_);
if (v_isSharedCheck_909_ == 0)
{
v___x_897_ = v_map_890_;
v_isShared_898_ = v_isSharedCheck_909_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_indexes_895_);
lean_inc(v_entries_894_);
lean_dec(v_map_890_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_909_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_idxs_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v_lastIdx_903_; lean_object* v___x_904_; lean_object* v_entries_905_; lean_object* v___x_907_; 
lean_inc(v_key_891_);
v_idxs_899_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_888_, v_inst_889_, v_indexes_895_, v_key_891_);
v___x_900_ = lean_array_get_size(v_idxs_899_);
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_nat_sub(v___x_900_, v___x_901_);
v_lastIdx_903_ = lean_array_fget(v_idxs_899_, v___x_902_);
lean_dec(v___x_902_);
lean_dec(v_idxs_899_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v_key_891_);
lean_ctor_set(v___x_904_, 1, v_value_892_);
v_entries_905_ = lean_array_fset(v_entries_894_, v_lastIdx_903_, v___x_904_);
lean_dec(v_lastIdx_903_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_entries_905_);
v___x_907_ = v___x_897_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_entries_905_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_indexes_895_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast(lean_object* v_00_u03b1_910_, lean_object* v_00_u03b2_911_, lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_map_914_, lean_object* v_key_915_, lean_object* v_value_916_){
_start:
{
uint8_t v___x_917_; 
lean_inc(v_key_915_);
lean_inc_ref(v_inst_913_);
lean_inc_ref(v_inst_912_);
v___x_917_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_912_, v_inst_913_, v_key_915_, v_map_914_);
if (v___x_917_ == 0)
{
lean_dec(v_value_916_);
lean_dec(v_key_915_);
lean_dec_ref(v_inst_913_);
lean_dec_ref(v_inst_912_);
return v_map_914_;
}
else
{
lean_object* v_entries_918_; lean_object* v_indexes_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_933_; 
v_entries_918_ = lean_ctor_get(v_map_914_, 0);
v_indexes_919_ = lean_ctor_get(v_map_914_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_map_914_);
if (v_isSharedCheck_933_ == 0)
{
v___x_921_ = v_map_914_;
v_isShared_922_ = v_isSharedCheck_933_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_indexes_919_);
lean_inc(v_entries_918_);
lean_dec(v_map_914_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_933_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_idxs_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_lastIdx_927_; lean_object* v___x_928_; lean_object* v_entries_929_; lean_object* v___x_931_; 
lean_inc(v_key_915_);
v_idxs_923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_912_, v_inst_913_, v_indexes_919_, v_key_915_);
v___x_924_ = lean_array_get_size(v_idxs_923_);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_sub(v___x_924_, v___x_925_);
v_lastIdx_927_ = lean_array_fget(v_idxs_923_, v___x_926_);
lean_dec(v___x_926_);
lean_dec(v_idxs_923_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_key_915_);
lean_ctor_set(v___x_928_, 1, v_value_916_);
v_entries_929_ = lean_array_fset(v_entries_918_, v_lastIdx_927_, v___x_928_);
lean_dec(v_lastIdx_927_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v_entries_929_);
v___x_931_ = v___x_921_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_entries_929_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_indexes_919_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(lean_object* v_inst_934_, lean_object* v_inst_935_, lean_object* v_x1_936_, lean_object* v_x2_937_){
_start:
{
lean_object* v_fst_938_; lean_object* v_entries_939_; lean_object* v_indexes_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_951_; 
v_fst_938_ = lean_ctor_get(v_x2_937_, 0);
lean_inc(v_fst_938_);
v_entries_939_ = lean_ctor_get(v_x1_936_, 0);
v_indexes_940_ = lean_ctor_get(v_x1_936_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v_x1_936_);
if (v_isSharedCheck_951_ == 0)
{
v___x_942_ = v_x1_936_;
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_indexes_940_);
lean_inc(v_entries_939_);
lean_dec(v_x1_936_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_i_944_; lean_object* v_f_945_; lean_object* v_entries_946_; lean_object* v_indexes_947_; lean_object* v___x_949_; 
v_i_944_ = lean_array_get_size(v_entries_939_);
v_f_945_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_945_, 0, v_i_944_);
v_entries_946_ = lean_array_push(v_entries_939_, v_x2_937_);
v_indexes_947_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_934_, v_inst_935_, v_indexes_940_, v_fst_938_, v_f_945_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v_indexes_947_);
lean_ctor_set(v___x_942_, 0, v_entries_946_);
v___x_949_ = v___x_942_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_entries_946_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_indexes_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__0(lean_object* v_inst_952_, lean_object* v_key_953_, lean_object* v_x1_954_, lean_object* v_x2_955_){
_start:
{
lean_object* v_fst_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_fst_956_ = lean_ctor_get(v_x2_955_, 0);
lean_inc(v_fst_956_);
v___x_957_ = lean_apply_2(v_inst_952_, v_fst_956_, v_key_953_);
v___x_958_ = lean_unbox(v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; 
v___x_959_ = lean_array_push(v_x1_954_, v_x2_955_);
return v___x_959_;
}
else
{
lean_dec_ref(v_x2_955_);
return v_x1_954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg(lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_map_962_, lean_object* v_key_963_){
_start:
{
uint8_t v___x_964_; 
lean_inc(v_key_963_);
lean_inc_ref(v_inst_961_);
lean_inc_ref(v_inst_960_);
v___x_964_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_960_, v_inst_961_, v_key_963_, v_map_962_);
if (v___x_964_ == 0)
{
lean_dec(v_key_963_);
lean_dec_ref(v_inst_961_);
lean_dec_ref(v_inst_960_);
return v_map_962_;
}
else
{
lean_object* v_entries_965_; lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___y_970_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v_entries_965_ = lean_ctor_get(v_map_962_, 0);
lean_inc_ref(v_entries_965_);
lean_dec_ref(v_map_962_);
lean_inc_ref(v_inst_961_);
lean_inc_ref(v_inst_960_);
v___f_966_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_966_, 0, v_inst_960_);
lean_closure_set(v___f_966_, 1, v_inst_961_);
v___x_967_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_960_, v_inst_961_);
lean_dec_ref(v_inst_961_);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_array_get_size(v_entries_965_);
v___x_982_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___closed__0));
v___x_983_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_984_ = lean_nat_dec_lt(v___x_968_, v___x_981_);
if (v___x_984_ == 0)
{
lean_dec_ref(v_entries_965_);
lean_dec(v_key_963_);
lean_dec_ref(v_inst_960_);
v___y_970_ = v___x_982_;
goto v___jp_969_;
}
else
{
lean_object* v___f_985_; uint8_t v___x_986_; 
v___f_985_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__0), 4, 2);
lean_closure_set(v___f_985_, 0, v_inst_960_);
lean_closure_set(v___f_985_, 1, v_key_963_);
v___x_986_ = lean_nat_dec_le(v___x_981_, v___x_981_);
if (v___x_986_ == 0)
{
if (v___x_984_ == 0)
{
lean_dec_ref(v___f_985_);
lean_dec_ref(v_entries_965_);
v___y_970_ = v___x_982_;
goto v___jp_969_;
}
else
{
size_t v___x_987_; size_t v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((size_t)0ULL);
v___x_988_ = lean_usize_of_nat(v___x_981_);
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_983_, v___f_985_, v_entries_965_, v___x_987_, v___x_988_, v___x_982_);
v___y_970_ = v___x_989_;
goto v___jp_969_;
}
}
else
{
size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; 
v___x_990_ = ((size_t)0ULL);
v___x_991_ = lean_usize_of_nat(v___x_981_);
v___x_992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_983_, v___f_985_, v_entries_965_, v___x_990_, v___x_991_, v___x_982_);
v___y_970_ = v___x_992_;
goto v___jp_969_;
}
}
v___jp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_971_ = lean_array_get_size(v___y_970_);
v___x_972_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_973_ = lean_nat_dec_lt(v___x_968_, v___x_971_);
if (v___x_973_ == 0)
{
lean_dec_ref(v___y_970_);
lean_dec_ref(v___f_966_);
return v___x_967_;
}
else
{
uint8_t v___x_974_; 
v___x_974_ = lean_nat_dec_le(v___x_971_, v___x_971_);
if (v___x_974_ == 0)
{
if (v___x_973_ == 0)
{
lean_dec_ref(v___y_970_);
lean_dec_ref(v___f_966_);
return v___x_967_;
}
else
{
size_t v___x_975_; size_t v___x_976_; lean_object* v___x_977_; 
v___x_975_ = ((size_t)0ULL);
v___x_976_ = lean_usize_of_nat(v___x_971_);
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_972_, v___f_966_, v___y_970_, v___x_975_, v___x_976_, v___x_967_);
return v___x_977_;
}
}
else
{
size_t v___x_978_; size_t v___x_979_; lean_object* v___x_980_; 
v___x_978_ = ((size_t)0ULL);
v___x_979_ = lean_usize_of_nat(v___x_971_);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_972_, v___f_966_, v___y_970_, v___x_978_, v___x_979_, v___x_967_);
return v___x_980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase(lean_object* v_00_u03b1_993_, lean_object* v_00_u03b2_994_, lean_object* v_inst_995_, lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_map_999_, lean_object* v_key_1000_){
_start:
{
uint8_t v___x_1001_; 
lean_inc(v_key_1000_);
lean_inc_ref(v_inst_996_);
lean_inc_ref(v_inst_995_);
v___x_1001_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_995_, v_inst_996_, v_key_1000_, v_map_999_);
if (v___x_1001_ == 0)
{
lean_dec(v_key_1000_);
lean_dec_ref(v_inst_996_);
lean_dec_ref(v_inst_995_);
return v_map_999_;
}
else
{
lean_object* v_entries_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___y_1007_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v_entries_1002_ = lean_ctor_get(v_map_999_, 0);
lean_inc_ref(v_entries_1002_);
lean_dec_ref(v_map_999_);
lean_inc_ref(v_inst_996_);
lean_inc_ref(v_inst_995_);
v___f_1003_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1003_, 0, v_inst_995_);
lean_closure_set(v___f_1003_, 1, v_inst_996_);
v___x_1004_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_995_, v_inst_996_);
lean_dec_ref(v_inst_996_);
v___x_1005_ = lean_unsigned_to_nat(0u);
v___x_1018_ = lean_array_get_size(v_entries_1002_);
v___x_1019_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___closed__0));
v___x_1020_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1021_ = lean_nat_dec_lt(v___x_1005_, v___x_1018_);
if (v___x_1021_ == 0)
{
lean_dec_ref(v_entries_1002_);
lean_dec(v_key_1000_);
lean_dec_ref(v_inst_995_);
v___y_1007_ = v___x_1019_;
goto v___jp_1006_;
}
else
{
lean_object* v___f_1022_; uint8_t v___x_1023_; 
v___f_1022_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1022_, 0, v_inst_995_);
lean_closure_set(v___f_1022_, 1, v_key_1000_);
v___x_1023_ = lean_nat_dec_le(v___x_1018_, v___x_1018_);
if (v___x_1023_ == 0)
{
if (v___x_1021_ == 0)
{
lean_dec_ref(v___f_1022_);
lean_dec_ref(v_entries_1002_);
v___y_1007_ = v___x_1019_;
goto v___jp_1006_;
}
else
{
size_t v___x_1024_; size_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = ((size_t)0ULL);
v___x_1025_ = lean_usize_of_nat(v___x_1018_);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1020_, v___f_1022_, v_entries_1002_, v___x_1024_, v___x_1025_, v___x_1019_);
v___y_1007_ = v___x_1026_;
goto v___jp_1006_;
}
}
else
{
size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = ((size_t)0ULL);
v___x_1028_ = lean_usize_of_nat(v___x_1018_);
v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1020_, v___f_1022_, v_entries_1002_, v___x_1027_, v___x_1028_, v___x_1019_);
v___y_1007_ = v___x_1029_;
goto v___jp_1006_;
}
}
v___jp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1008_ = lean_array_get_size(v___y_1007_);
v___x_1009_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1010_ = lean_nat_dec_lt(v___x_1005_, v___x_1008_);
if (v___x_1010_ == 0)
{
lean_dec_ref(v___y_1007_);
lean_dec_ref(v___f_1003_);
return v___x_1004_;
}
else
{
uint8_t v___x_1011_; 
v___x_1011_ = lean_nat_dec_le(v___x_1008_, v___x_1008_);
if (v___x_1011_ == 0)
{
if (v___x_1010_ == 0)
{
lean_dec_ref(v___y_1007_);
lean_dec_ref(v___f_1003_);
return v___x_1004_;
}
else
{
size_t v___x_1012_; size_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = ((size_t)0ULL);
v___x_1013_ = lean_usize_of_nat(v___x_1008_);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1009_, v___f_1003_, v___y_1007_, v___x_1012_, v___x_1013_, v___x_1004_);
return v___x_1014_;
}
}
else
{
size_t v___x_1015_; size_t v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = ((size_t)0ULL);
v___x_1016_ = lean_usize_of_nat(v___x_1008_);
v___x_1017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1009_, v___f_1003_, v___y_1007_, v___x_1015_, v___x_1016_, v___x_1004_);
return v___x_1017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg(lean_object* v_map_1030_){
_start:
{
lean_object* v_entries_1031_; lean_object* v___x_1032_; 
v_entries_1031_ = lean_ctor_get(v_map_1030_, 0);
v___x_1032_ = lean_array_get_size(v_entries_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg___boxed(lean_object* v_map_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Std_Internal_IndexMultiMap_size___redArg(v_map_1033_);
lean_dec_ref(v_map_1033_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size(lean_object* v_00_u03b1_1035_, lean_object* v_00_u03b2_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_map_1039_){
_start:
{
lean_object* v_entries_1040_; lean_object* v___x_1041_; 
v_entries_1040_ = lean_ctor_get(v_map_1039_, 0);
v___x_1041_ = lean_array_get_size(v_entries_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_map_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Std_Internal_IndexMultiMap_size(v_00_u03b1_1042_, v_00_u03b2_1043_, v_inst_1044_, v_inst_1045_, v_map_1046_);
lean_dec_ref(v_map_1046_);
lean_dec_ref(v_inst_1045_);
lean_dec_ref(v_inst_1044_);
return v_res_1047_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty___redArg(lean_object* v_map_1048_){
_start:
{
lean_object* v_entries_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_entries_1049_ = lean_ctor_get(v_map_1048_, 0);
v___x_1050_ = lean_array_get_size(v_entries_1049_);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = lean_nat_dec_eq(v___x_1050_, v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___redArg___boxed(lean_object* v_map_1053_){
_start:
{
uint8_t v_res_1054_; lean_object* v_r_1055_; 
v_res_1054_ = l_Std_Internal_IndexMultiMap_isEmpty___redArg(v_map_1053_);
lean_dec_ref(v_map_1053_);
v_r_1055_ = lean_box(v_res_1054_);
return v_r_1055_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty(lean_object* v_00_u03b1_1056_, lean_object* v_00_u03b2_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_map_1060_){
_start:
{
lean_object* v_entries_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v_entries_1061_ = lean_ctor_get(v_map_1060_, 0);
v___x_1062_ = lean_array_get_size(v_entries_1061_);
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = lean_nat_dec_eq(v___x_1062_, v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___boxed(lean_object* v_00_u03b1_1065_, lean_object* v_00_u03b2_1066_, lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_map_1069_){
_start:
{
uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Std_Internal_IndexMultiMap_isEmpty(v_00_u03b1_1065_, v_00_u03b2_1066_, v_inst_1067_, v_inst_1068_, v_map_1069_);
lean_dec_ref(v_map_1069_);
lean_dec_ref(v_inst_1068_);
lean_dec_ref(v_inst_1067_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg(lean_object* v_map_1072_){
_start:
{
lean_object* v_entries_1073_; 
v_entries_1073_ = lean_ctor_get(v_map_1072_, 0);
lean_inc_ref(v_entries_1073_);
return v_entries_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg___boxed(lean_object* v_map_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Std_Internal_IndexMultiMap_toArray___redArg(v_map_1074_);
lean_dec_ref(v_map_1074_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray(lean_object* v_00_u03b1_1076_, lean_object* v_00_u03b2_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_map_1080_){
_start:
{
lean_object* v_entries_1081_; 
v_entries_1081_ = lean_ctor_get(v_map_1080_, 0);
lean_inc_ref(v_entries_1081_);
return v_entries_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___boxed(lean_object* v_00_u03b1_1082_, lean_object* v_00_u03b2_1083_, lean_object* v_inst_1084_, lean_object* v_inst_1085_, lean_object* v_map_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Std_Internal_IndexMultiMap_toArray(v_00_u03b1_1082_, v_00_u03b2_1083_, v_inst_1084_, v_inst_1085_, v_map_1086_);
lean_dec_ref(v_map_1086_);
lean_dec_ref(v_inst_1085_);
lean_dec_ref(v_inst_1084_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___redArg(lean_object* v_map_1088_){
_start:
{
lean_object* v_entries_1089_; lean_object* v___x_1090_; 
v_entries_1089_ = lean_ctor_get(v_map_1088_, 0);
lean_inc_ref(v_entries_1089_);
lean_dec_ref(v_map_1088_);
v___x_1090_ = lean_array_to_list(v_entries_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList(lean_object* v_00_u03b1_1091_, lean_object* v_00_u03b2_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_map_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Std_Internal_IndexMultiMap_toList___redArg(v_map_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___boxed(lean_object* v_00_u03b1_1097_, lean_object* v_00_u03b2_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_map_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_Internal_IndexMultiMap_toList(v_00_u03b1_1097_, v_00_u03b2_1098_, v_inst_1099_, v_inst_1100_, v_map_1101_);
lean_dec_ref(v_inst_1100_);
lean_dec_ref(v_inst_1099_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg(lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_m1_1105_, lean_object* v_m2_1106_){
_start:
{
lean_object* v_entries_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_entries_1107_ = lean_ctor_get(v_m2_1106_, 0);
lean_inc_ref(v_entries_1107_);
lean_dec_ref(v_m2_1106_);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_array_get_size(v_entries_1107_);
v___x_1110_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1111_ = lean_nat_dec_lt(v___x_1108_, v___x_1109_);
if (v___x_1111_ == 0)
{
lean_dec_ref(v_entries_1107_);
lean_dec_ref(v_inst_1104_);
lean_dec_ref(v_inst_1103_);
return v_m1_1105_;
}
else
{
lean_object* v___f_1112_; uint8_t v___x_1113_; 
v___f_1112_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1112_, 0, v_inst_1103_);
lean_closure_set(v___f_1112_, 1, v_inst_1104_);
v___x_1113_ = lean_nat_dec_le(v___x_1109_, v___x_1109_);
if (v___x_1113_ == 0)
{
if (v___x_1111_ == 0)
{
lean_dec_ref(v___f_1112_);
lean_dec_ref(v_entries_1107_);
return v_m1_1105_;
}
else
{
size_t v___x_1114_; size_t v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = ((size_t)0ULL);
v___x_1115_ = lean_usize_of_nat(v___x_1109_);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1110_, v___f_1112_, v_entries_1107_, v___x_1114_, v___x_1115_, v_m1_1105_);
return v___x_1116_;
}
}
else
{
size_t v___x_1117_; size_t v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = ((size_t)0ULL);
v___x_1118_ = lean_usize_of_nat(v___x_1109_);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1110_, v___f_1112_, v_entries_1107_, v___x_1117_, v___x_1118_, v_m1_1105_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge(lean_object* v_00_u03b1_1120_, lean_object* v_00_u03b2_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_m1_1126_, lean_object* v_m2_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Std_Internal_IndexMultiMap_merge___redArg(v_inst_1122_, v_inst_1123_, v_m1_1126_, v_m2_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(lean_object* v_inst_1129_, lean_object* v_inst_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1129_, v_inst_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object* v_inst_1132_, lean_object* v_inst_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(v_inst_1132_, v_inst_1133_);
lean_dec_ref(v_inst_1133_);
lean_dec_ref(v_inst_1132_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection(lean_object* v_00_u03b1_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1137_, v_inst_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_1140_, lean_object* v_00_u03b2_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_Internal_IndexMultiMap_instEmptyCollection(v_00_u03b1_1140_, v_00_u03b2_1141_, v_inst_1142_, v_inst_1143_);
lean_dec_ref(v_inst_1143_);
lean_dec_ref(v_inst_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v_fst_1148_; lean_object* v___x_1149_; lean_object* v_entries_1150_; lean_object* v_indexes_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1162_; 
v_fst_1148_ = lean_ctor_get(v_x_1147_, 0);
lean_inc(v_fst_1148_);
v___x_1149_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1145_, v_inst_1146_);
v_entries_1150_ = lean_ctor_get(v___x_1149_, 0);
v_indexes_1151_ = lean_ctor_get(v___x_1149_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1153_ = v___x_1149_;
v_isShared_1154_ = v_isSharedCheck_1162_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_indexes_1151_);
lean_inc(v_entries_1150_);
lean_dec(v___x_1149_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1162_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_i_1155_; lean_object* v_f_1156_; lean_object* v_entries_1157_; lean_object* v_indexes_1158_; lean_object* v___x_1160_; 
v_i_1155_ = lean_array_get_size(v_entries_1150_);
v_f_1156_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1156_, 0, v_i_1155_);
v_entries_1157_ = lean_array_push(v_entries_1150_, v_x_1147_);
v_indexes_1158_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1145_, v_inst_1146_, v_indexes_1151_, v_fst_1148_, v_f_1156_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v_indexes_1158_);
lean_ctor_set(v___x_1153_, 0, v_entries_1157_);
v___x_1160_ = v___x_1153_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_entries_1157_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_indexes_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1163_, lean_object* v_inst_1164_){
_start:
{
lean_object* v___f_1165_; 
v___f_1165_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1165_, 0, v_inst_1163_);
lean_closure_set(v___f_1165_, 1, v_inst_1164_);
return v___f_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1166_, lean_object* v_00_u03b2_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_){
_start:
{
lean_object* v___f_1172_; 
v___f_1172_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1172_, 0, v_inst_1168_);
lean_closure_set(v___f_1172_, 1, v_inst_1169_);
return v___f_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_x_1175_, lean_object* v_m_1176_){
_start:
{
lean_object* v_fst_1177_; lean_object* v_entries_1178_; lean_object* v_indexes_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1190_; 
v_fst_1177_ = lean_ctor_get(v_x_1175_, 0);
lean_inc(v_fst_1177_);
v_entries_1178_ = lean_ctor_get(v_m_1176_, 0);
v_indexes_1179_ = lean_ctor_get(v_m_1176_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_m_1176_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1181_ = v_m_1176_;
v_isShared_1182_ = v_isSharedCheck_1190_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_indexes_1179_);
lean_inc(v_entries_1178_);
lean_dec(v_m_1176_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1190_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_i_1183_; lean_object* v_f_1184_; lean_object* v_entries_1185_; lean_object* v_indexes_1186_; lean_object* v___x_1188_; 
v_i_1183_ = lean_array_get_size(v_entries_1178_);
v_f_1184_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1184_, 0, v_i_1183_);
v_entries_1185_ = lean_array_push(v_entries_1178_, v_x_1175_);
v_indexes_1186_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1173_, v_inst_1174_, v_indexes_1179_, v_fst_1177_, v_f_1184_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v_indexes_1186_);
lean_ctor_set(v___x_1181_, 0, v_entries_1185_);
v___x_1188_ = v___x_1181_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_entries_1185_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_indexes_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1191_, lean_object* v_inst_1192_){
_start:
{
lean_object* v___f_1193_; 
v___f_1193_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1193_, 0, v_inst_1191_);
lean_closure_set(v___f_1193_, 1, v_inst_1192_);
return v___f_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_){
_start:
{
lean_object* v___f_1200_; 
v___f_1200_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1200_, 0, v_inst_1196_);
lean_closure_set(v___f_1200_, 1, v_inst_1197_);
return v___f_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1201_, lean_object* v_inst_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1203_, 0, lean_box(0));
lean_closure_set(v___x_1203_, 1, lean_box(0));
lean_closure_set(v___x_1203_, 2, v_inst_1201_);
lean_closure_set(v___x_1203_, 3, v_inst_1202_);
lean_closure_set(v___x_1203_, 4, lean_box(0));
lean_closure_set(v___x_1203_, 5, lean_box(0));
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1204_, lean_object* v_00_u03b2_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1210_, 0, lean_box(0));
lean_closure_set(v___x_1210_, 1, lean_box(0));
lean_closure_set(v___x_1210_, 2, v_inst_1206_);
lean_closure_set(v___x_1210_, 3, v_inst_1207_);
lean_closure_set(v___x_1210_, 4, lean_box(0));
lean_closure_set(v___x_1210_, 5, lean_box(0));
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1211_, lean_object* v_a_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_apply_2(v_f_1211_, v_a_1212_, v___y_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1216_, lean_object* v_00_u03b2_1217_, lean_object* v_map_1218_, lean_object* v_b_1219_, lean_object* v_f_1220_){
_start:
{
lean_object* v_entries_1221_; lean_object* v___f_1222_; size_t v_sz_1223_; size_t v___x_1224_; lean_object* v___x_1225_; 
v_entries_1221_ = lean_ctor_get(v_map_1218_, 0);
lean_inc_ref(v_entries_1221_);
lean_dec_ref(v_map_1218_);
v___f_1222_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1222_, 0, v_f_1220_);
v_sz_1223_ = lean_array_size(v_entries_1221_);
v___x_1224_ = ((size_t)0ULL);
v___x_1225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1216_, v_entries_1221_, v___f_1222_, v_sz_1223_, v___x_1224_, v_b_1219_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg(lean_object* v_inst_1226_){
_start:
{
lean_object* v___f_1227_; 
v___f_1227_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1227_, 0, v_inst_1226_);
return v___f_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad(lean_object* v_00_u03b1_1228_, lean_object* v_00_u03b2_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_m_1232_, lean_object* v_inst_1233_){
_start:
{
lean_object* v___f_1234_; 
v___f_1234_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1234_, 0, v_inst_1233_);
return v___f_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1235_, lean_object* v_00_u03b2_1236_, lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_m_1239_, lean_object* v_inst_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Std_Internal_IndexMultiMap_instForInProdOfMonad(v_00_u03b1_1235_, v_00_u03b2_1236_, v_inst_1237_, v_inst_1238_, v_m_1239_, v_inst_1240_);
lean_dec_ref(v_inst_1238_);
lean_dec_ref(v_inst_1237_);
return v_res_1241_;
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
