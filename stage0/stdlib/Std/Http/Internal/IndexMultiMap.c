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
lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg(){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3);
return v___x_190_;
}
}
LEAN_EXPORT void l_Std_Internal_instInhabitedIndexMultiMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_191_;
v_res_191_ = l_Std_Internal_instInhabitedIndexMultiMap___redArg();
stack->m_obj
 = v_res_191_;
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___boxed(lean_object* v___dummy_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Internal_instInhabitedIndexMultiMap___redArg();
return v_res_193_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__0(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_Internal_instInhabitedIndexMultiMap___redArg();
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_inst_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__0, &l_Std_Internal_instInhabitedIndexMultiMap___closed__0_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__0);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___boxed(lean_object* v_00_u03b1_202_, lean_object* v_00_u03b2_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_inst_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Internal_instInhabitedIndexMultiMap(v_00_u03b1_202_, v_00_u03b2_203_, v_inst_204_, v_inst_205_, v_inst_206_, v_inst_207_);
lean_dec(v_inst_207_);
lean_dec(v_inst_206_);
lean_dec_ref(v_inst_205_);
lean_dec_ref(v_inst_204_);
return v_res_208_;
}
}
lean_object* l_Std_Internal_IndexMultiMap_instMembership___redArg(){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lean_box(0);
return v___x_210_;
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_211_;
v_res_211_ = l_Std_Internal_IndexMultiMap_instMembership___redArg();
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___redArg___boxed(lean_object* v___dummy_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Internal_IndexMultiMap_instMembership___redArg();
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_inst_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(0);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___boxed(lean_object* v_00_u03b1_219_, lean_object* v_00_u03b2_220_, lean_object* v_inst_221_, lean_object* v_inst_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Std_Internal_IndexMultiMap_instMembership(v_00_u03b1_219_, v_00_u03b2_220_, v_inst_221_, v_inst_222_);
lean_dec_ref(v_inst_222_);
lean_dec_ref(v_inst_221_);
return v_res_223_;
}
}
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_key_226_, lean_object* v_map_227_){
_start:
{
lean_object* v_indexes_228_; uint8_t v___x_229_; 
v_indexes_228_ = lean_ctor_get(v_map_227_, 1);
v___x_229_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_224_, v_inst_225_, v_indexes_228_, v_key_226_);
return v___x_229_;
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_224_ = stack[0].m_obj;
lean_object* v_inst_225_ = stack[1].m_obj;
lean_object* v_key_226_ = stack[2].m_obj;
lean_object* v_map_227_ = stack[3].m_obj;
uint8_t v_res_230_;
v_res_230_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_224_, v_inst_225_, v_key_226_, v_map_227_);
stack->m_num = v_res_230_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___redArg___boxed(lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_key_233_, lean_object* v_map_234_){
_start:
{
uint8_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_231_, v_inst_232_, v_key_233_, v_map_234_);
lean_dec_ref(v_map_234_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem(lean_object* v_00_u03b1_237_, lean_object* v_00_u03b2_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_key_241_, lean_object* v_map_242_){
_start:
{
uint8_t v___x_243_; 
v___x_243_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_239_, v_inst_240_, v_key_241_, v_map_242_);
return v___x_243_;
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_239_ = stack[2].m_obj;
lean_object* v_inst_240_ = stack[3].m_obj;
lean_object* v_key_241_ = stack[4].m_obj;
lean_object* v_map_242_ = stack[5].m_obj;
uint8_t v_res_244_;
v_res_244_ = l_Std_Internal_IndexMultiMap_instDecidableMem(lean_box(0), lean_box(0), v_inst_239_, v_inst_240_, v_key_241_, v_map_242_);
stack->m_num = v_res_244_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___boxed(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_key_249_, lean_object* v_map_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Std_Internal_IndexMultiMap_instDecidableMem(v_00_u03b1_245_, v_00_u03b2_246_, v_inst_247_, v_inst_248_, v_key_249_, v_map_250_);
lean_dec_ref(v_map_250_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(lean_object* v___x_253_, lean_object* v_entries_254_, lean_object* v_x1_255_, lean_object* v_x2_256_, lean_object* v_x3_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v_snd_260_; 
v___x_258_ = lean_array_fget_borrowed(v___x_253_, v_x1_255_);
v___x_259_ = lean_array_fget_borrowed(v_entries_254_, v___x_258_);
v_snd_260_ = lean_ctor_get(v___x_259_, 1);
lean_inc(v_snd_260_);
return v_snd_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed(lean_object* v___x_261_, lean_object* v_entries_262_, lean_object* v_x1_263_, lean_object* v_x2_264_, lean_object* v_x3_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(v___x_261_, v_entries_262_, v_x1_263_, v_x2_264_, v_x3_265_);
lean_dec(v_x2_264_);
lean_dec(v_x1_263_);
lean_dec_ref(v_entries_262_);
lean_dec(v___x_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg(lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_map_269_, lean_object* v_key_270_){
_start:
{
lean_object* v_entries_271_; lean_object* v_indexes_272_; lean_object* v___x_273_; lean_object* v___f_274_; lean_object* v___x_275_; size_t v_sz_276_; size_t v___x_277_; lean_object* v_entries_278_; 
v_entries_271_ = lean_ctor_get(v_map_269_, 0);
lean_inc_ref(v_entries_271_);
v_indexes_272_ = lean_ctor_get(v_map_269_, 1);
lean_inc_ref(v_indexes_272_);
lean_dec_ref(v_map_269_);
v___x_273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_267_, v_inst_268_, v_indexes_272_, v_key_270_);
lean_dec_ref(v_indexes_272_);
lean_inc_n(v___x_273_, 2);
v___f_274_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_274_, 0, v___x_273_);
lean_closure_set(v___f_274_, 1, v_entries_271_);
v___x_275_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_276_ = lean_array_size(v___x_273_);
v___x_277_ = ((size_t)0ULL);
v_entries_278_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_275_, v___x_273_, v___f_274_, v_sz_276_, v___x_277_, v___x_273_);
lean_dec(v___x_273_);
return v_entries_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll(lean_object* v_00_u03b1_279_, lean_object* v_00_u03b2_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_map_283_, lean_object* v_key_284_, lean_object* v_h_285_){
_start:
{
lean_object* v_entries_286_; lean_object* v_indexes_287_; lean_object* v___x_288_; lean_object* v___f_289_; lean_object* v___x_290_; size_t v_sz_291_; size_t v___x_292_; lean_object* v_entries_293_; 
v_entries_286_ = lean_ctor_get(v_map_283_, 0);
lean_inc_ref(v_entries_286_);
v_indexes_287_ = lean_ctor_get(v_map_283_, 1);
lean_inc_ref(v_indexes_287_);
lean_dec_ref(v_map_283_);
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_281_, v_inst_282_, v_indexes_287_, v_key_284_);
lean_dec_ref(v_indexes_287_);
lean_inc_n(v___x_288_, 2);
v___f_289_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_289_, 0, v___x_288_);
lean_closure_set(v___f_289_, 1, v_entries_286_);
v___x_290_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_291_ = lean_array_size(v___x_288_);
v___x_292_ = ((size_t)0ULL);
v_entries_293_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_290_, v___x_288_, v___f_289_, v_sz_291_, v___x_292_, v___x_288_);
lean_dec(v___x_288_);
return v_entries_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg(lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_map_296_, lean_object* v_key_297_){
_start:
{
lean_object* v_entries_298_; lean_object* v_indexes_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_entry_302_; lean_object* v___x_303_; lean_object* v_snd_304_; 
v_entries_298_ = lean_ctor_get(v_map_296_, 0);
v_indexes_299_ = lean_ctor_get(v_map_296_, 1);
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_294_, v_inst_295_, v_indexes_299_, v_key_297_);
v___x_301_ = lean_unsigned_to_nat(0u);
v_entry_302_ = lean_array_fget(v___x_300_, v___x_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_array_fget_borrowed(v_entries_298_, v_entry_302_);
lean_dec(v_entry_302_);
v_snd_304_ = lean_ctor_get(v___x_303_, 1);
lean_inc(v_snd_304_);
return v_snd_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg___boxed(lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_map_307_, lean_object* v_key_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Internal_IndexMultiMap_get___redArg(v_inst_305_, v_inst_306_, v_map_307_, v_key_308_);
lean_dec_ref(v_map_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get(lean_object* v_00_u03b1_310_, lean_object* v_00_u03b2_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_map_314_, lean_object* v_key_315_, lean_object* v_h_316_){
_start:
{
lean_object* v_entries_317_; lean_object* v_indexes_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_entry_321_; lean_object* v___x_322_; lean_object* v_snd_323_; 
v_entries_317_ = lean_ctor_get(v_map_314_, 0);
v_indexes_318_ = lean_ctor_get(v_map_314_, 1);
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_312_, v_inst_313_, v_indexes_318_, v_key_315_);
v___x_320_ = lean_unsigned_to_nat(0u);
v_entry_321_ = lean_array_fget(v___x_319_, v___x_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_array_fget_borrowed(v_entries_317_, v_entry_321_);
lean_dec(v_entry_321_);
v_snd_323_ = lean_ctor_get(v___x_322_, 1);
lean_inc(v_snd_323_);
return v_snd_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___boxed(lean_object* v_00_u03b1_324_, lean_object* v_00_u03b2_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_map_328_, lean_object* v_key_329_, lean_object* v_h_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_Internal_IndexMultiMap_get(v_00_u03b1_324_, v_00_u03b2_325_, v_inst_326_, v_inst_327_, v_map_328_, v_key_329_, v_h_330_);
lean_dec_ref(v_map_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f___redArg(lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_map_334_, lean_object* v_key_335_){
_start:
{
lean_object* v_entries_336_; lean_object* v_indexes_337_; uint8_t v___x_338_; 
v_entries_336_ = lean_ctor_get(v_map_334_, 0);
lean_inc_ref(v_entries_336_);
v_indexes_337_ = lean_ctor_get(v_map_334_, 1);
lean_inc_ref(v_indexes_337_);
lean_dec_ref(v_map_334_);
lean_inc(v_key_335_);
lean_inc_ref(v_inst_333_);
lean_inc_ref(v_inst_332_);
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_332_, v_inst_333_, v_indexes_337_, v_key_335_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
lean_dec_ref(v_indexes_337_);
lean_dec_ref(v_entries_336_);
lean_dec(v_key_335_);
lean_dec_ref(v_inst_333_);
lean_dec_ref(v_inst_332_);
v___x_339_ = lean_box(0);
return v___x_339_;
}
else
{
lean_object* v___x_340_; lean_object* v___f_341_; lean_object* v___x_342_; size_t v_sz_343_; size_t v___x_344_; lean_object* v_entries_345_; lean_object* v___x_346_; 
v___x_340_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_332_, v_inst_333_, v_indexes_337_, v_key_335_);
lean_dec_ref(v_indexes_337_);
lean_inc_n(v___x_340_, 2);
v___f_341_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_341_, 0, v___x_340_);
lean_closure_set(v___f_341_, 1, v_entries_336_);
v___x_342_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_343_ = lean_array_size(v___x_340_);
v___x_344_ = ((size_t)0ULL);
v_entries_345_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_342_, v___x_340_, v___f_341_, v_sz_343_, v___x_344_, v___x_340_);
lean_dec(v___x_340_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v_entries_345_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f(lean_object* v_00_u03b1_347_, lean_object* v_00_u03b2_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_map_351_, lean_object* v_key_352_){
_start:
{
lean_object* v_entries_353_; lean_object* v_indexes_354_; uint8_t v___x_355_; 
v_entries_353_ = lean_ctor_get(v_map_351_, 0);
lean_inc_ref(v_entries_353_);
v_indexes_354_ = lean_ctor_get(v_map_351_, 1);
lean_inc_ref(v_indexes_354_);
lean_dec_ref(v_map_351_);
lean_inc(v_key_352_);
lean_inc_ref(v_inst_350_);
lean_inc_ref(v_inst_349_);
v___x_355_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_349_, v_inst_350_, v_indexes_354_, v_key_352_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec_ref(v_indexes_354_);
lean_dec_ref(v_entries_353_);
lean_dec(v_key_352_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
v___x_356_ = lean_box(0);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v___f_358_; lean_object* v___x_359_; size_t v_sz_360_; size_t v___x_361_; lean_object* v_entries_362_; lean_object* v___x_363_; 
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_349_, v_inst_350_, v_indexes_354_, v_key_352_);
lean_dec_ref(v_indexes_354_);
lean_inc_n(v___x_357_, 2);
v___f_358_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_358_, 0, v___x_357_);
lean_closure_set(v___f_358_, 1, v_entries_353_);
v___x_359_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_360_ = lean_array_size(v___x_357_);
v___x_361_ = ((size_t)0ULL);
v_entries_362_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_359_, v___x_357_, v___f_358_, v_sz_360_, v___x_361_, v___x_357_);
lean_dec(v___x_357_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v_entries_362_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg(lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_map_366_, lean_object* v_key_367_){
_start:
{
lean_object* v_entries_368_; lean_object* v_indexes_369_; uint8_t v___x_370_; 
v_entries_368_ = lean_ctor_get(v_map_366_, 0);
v_indexes_369_ = lean_ctor_get(v_map_366_, 1);
lean_inc(v_key_367_);
lean_inc_ref(v_inst_365_);
lean_inc_ref(v_inst_364_);
v___x_370_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_364_, v_inst_365_, v_indexes_369_, v_key_367_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec(v_key_367_);
lean_dec_ref(v_inst_365_);
lean_dec_ref(v_inst_364_);
v___x_371_ = lean_box(0);
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_entry_374_; lean_object* v___x_375_; lean_object* v_snd_376_; lean_object* v___x_377_; 
v___x_372_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_364_, v_inst_365_, v_indexes_369_, v_key_367_);
v___x_373_ = lean_unsigned_to_nat(0u);
v_entry_374_ = lean_array_fget(v___x_372_, v___x_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_array_fget_borrowed(v_entries_368_, v_entry_374_);
lean_dec(v_entry_374_);
v_snd_376_ = lean_ctor_get(v___x_375_, 1);
lean_inc(v_snd_376_);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v_snd_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg___boxed(lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_map_380_, lean_object* v_key_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_Internal_IndexMultiMap_get_x3f___redArg(v_inst_378_, v_inst_379_, v_map_380_, v_key_381_);
lean_dec_ref(v_map_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f(lean_object* v_00_u03b1_383_, lean_object* v_00_u03b2_384_, lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_map_387_, lean_object* v_key_388_){
_start:
{
lean_object* v_entries_389_; lean_object* v_indexes_390_; uint8_t v___x_391_; 
v_entries_389_ = lean_ctor_get(v_map_387_, 0);
v_indexes_390_ = lean_ctor_get(v_map_387_, 1);
lean_inc(v_key_388_);
lean_inc_ref(v_inst_386_);
lean_inc_ref(v_inst_385_);
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_385_, v_inst_386_, v_indexes_390_, v_key_388_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
lean_dec(v_key_388_);
lean_dec_ref(v_inst_386_);
lean_dec_ref(v_inst_385_);
v___x_392_ = lean_box(0);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_entry_395_; lean_object* v___x_396_; lean_object* v_snd_397_; lean_object* v___x_398_; 
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_385_, v_inst_386_, v_indexes_390_, v_key_388_);
v___x_394_ = lean_unsigned_to_nat(0u);
v_entry_395_ = lean_array_fget(v___x_393_, v___x_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_array_fget_borrowed(v_entries_389_, v_entry_395_);
lean_dec(v_entry_395_);
v_snd_397_ = lean_ctor_get(v___x_396_, 1);
lean_inc(v_snd_397_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v_snd_397_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___boxed(lean_object* v_00_u03b1_399_, lean_object* v_00_u03b2_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_map_403_, lean_object* v_key_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_Internal_IndexMultiMap_get_x3f(v_00_u03b1_399_, v_00_u03b2_400_, v_inst_401_, v_inst_402_, v_map_403_, v_key_404_);
lean_dec_ref(v_map_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(lean_object* v_inst_406_, lean_object* v_value_407_, lean_object* v___x_408_, lean_object* v___x_409_, lean_object* v_a_410_, lean_object* v_x_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_413_; uint8_t v___x_414_; 
lean_inc(v_a_410_);
v___x_413_ = lean_apply_2(v_inst_406_, v_a_410_, v_value_407_);
v___x_414_ = lean_unbox(v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_dec(v_a_410_);
v___x_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_408_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec_ref(v___x_408_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v_a_410_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v___x_409_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed(lean_object* v_inst_420_, lean_object* v_value_421_, lean_object* v___x_422_, lean_object* v___x_423_, lean_object* v_a_424_, lean_object* v_x_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(v_inst_420_, v_value_421_, v___x_422_, v___x_423_, v_a_424_, v_x_425_, v___y_426_);
lean_dec_ref(v___y_426_);
return v_res_427_;
}
}
uint8_t l_Std_Internal_IndexMultiMap_hasEntry___redArg(lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_map_433_, lean_object* v_inst_434_, lean_object* v_key_435_, lean_object* v_value_436_){
_start:
{
lean_object* v_entries_437_; lean_object* v_indexes_438_; uint8_t v___x_439_; 
v_entries_437_ = lean_ctor_get(v_map_433_, 0);
lean_inc_ref(v_entries_437_);
v_indexes_438_ = lean_ctor_get(v_map_433_, 1);
lean_inc_ref(v_indexes_438_);
lean_dec_ref(v_map_433_);
lean_inc(v_key_435_);
lean_inc_ref(v_inst_432_);
lean_inc_ref(v_inst_431_);
v___x_439_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_431_, v_inst_432_, v_indexes_438_, v_key_435_);
if (v___x_439_ == 0)
{
lean_dec_ref(v_indexes_438_);
lean_dec_ref(v_entries_437_);
lean_dec(v_value_436_);
lean_dec(v_key_435_);
lean_dec_ref(v_inst_434_);
lean_dec_ref(v_inst_432_);
lean_dec_ref(v_inst_431_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; lean_object* v___f_441_; lean_object* v___x_442_; size_t v_sz_443_; size_t v___x_444_; lean_object* v_entries_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___f_448_; size_t v_sz_449_; lean_object* v___x_450_; lean_object* v_fst_451_; 
v___x_440_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_431_, v_inst_432_, v_indexes_438_, v_key_435_);
lean_dec_ref(v_indexes_438_);
lean_inc_n(v___x_440_, 2);
v___f_441_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_441_, 0, v___x_440_);
lean_closure_set(v___f_441_, 1, v_entries_437_);
v___x_442_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_443_ = lean_array_size(v___x_440_);
v___x_444_ = ((size_t)0ULL);
v_entries_445_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_442_, v___x_440_, v___f_441_, v_sz_443_, v___x_444_, v___x_440_);
lean_dec(v___x_440_);
v___x_446_ = lean_box(0);
v___x_447_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_448_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_448_, 0, v_inst_434_);
lean_closure_set(v___f_448_, 1, v_value_436_);
lean_closure_set(v___f_448_, 2, v___x_447_);
lean_closure_set(v___f_448_, 3, v___x_446_);
v_sz_449_ = lean_array_size(v_entries_445_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_442_, v_entries_445_, v___f_448_, v_sz_449_, v___x_444_, v___x_447_);
v_fst_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_fst_451_);
lean_dec(v___x_450_);
if (lean_obj_tag(v_fst_451_) == 0)
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
}
else
{
lean_object* v_val_453_; 
v_val_453_ = lean_ctor_get(v_fst_451_, 0);
lean_inc(v_val_453_);
lean_dec_ref_known(v_fst_451_, 1);
if (lean_obj_tag(v_val_453_) == 0)
{
uint8_t v___x_454_; 
v___x_454_ = 0;
return v___x_454_;
}
else
{
lean_dec_ref_known(v_val_453_, 1);
return v___x_439_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_hasEntry___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_431_ = stack[0].m_obj;
lean_object* v_inst_432_ = stack[1].m_obj;
lean_object* v_map_433_ = stack[2].m_obj;
lean_object* v_inst_434_ = stack[3].m_obj;
lean_object* v_key_435_ = stack[4].m_obj;
lean_object* v_value_436_ = stack[5].m_obj;
uint8_t v_res_455_;
v_res_455_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg(v_inst_431_, v_inst_432_, v_map_433_, v_inst_434_, v_key_435_, v_value_436_);
stack->m_num = v_res_455_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___boxed(lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_map_458_, lean_object* v_inst_459_, lean_object* v_key_460_, lean_object* v_value_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg(v_inst_456_, v_inst_457_, v_map_458_, v_inst_459_, v_key_460_, v_value_461_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
uint8_t l_Std_Internal_IndexMultiMap_hasEntry(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_map_468_, lean_object* v_inst_469_, lean_object* v_key_470_, lean_object* v_value_471_){
_start:
{
lean_object* v_entries_472_; lean_object* v_indexes_473_; uint8_t v___x_474_; 
v_entries_472_ = lean_ctor_get(v_map_468_, 0);
lean_inc_ref(v_entries_472_);
v_indexes_473_ = lean_ctor_get(v_map_468_, 1);
lean_inc_ref(v_indexes_473_);
lean_dec_ref(v_map_468_);
lean_inc(v_key_470_);
lean_inc_ref(v_inst_467_);
lean_inc_ref(v_inst_466_);
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_466_, v_inst_467_, v_indexes_473_, v_key_470_);
if (v___x_474_ == 0)
{
lean_dec_ref(v_indexes_473_);
lean_dec_ref(v_entries_472_);
lean_dec(v_value_471_);
lean_dec(v_key_470_);
lean_dec_ref(v_inst_469_);
lean_dec_ref(v_inst_467_);
lean_dec_ref(v_inst_466_);
return v___x_474_;
}
else
{
lean_object* v___x_475_; lean_object* v___f_476_; lean_object* v___x_477_; size_t v_sz_478_; size_t v___x_479_; lean_object* v_entries_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___f_483_; size_t v_sz_484_; lean_object* v___x_485_; lean_object* v_fst_486_; 
v___x_475_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_466_, v_inst_467_, v_indexes_473_, v_key_470_);
lean_dec_ref(v_indexes_473_);
lean_inc_n(v___x_475_, 2);
v___f_476_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_476_, 0, v___x_475_);
lean_closure_set(v___f_476_, 1, v_entries_472_);
v___x_477_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_478_ = lean_array_size(v___x_475_);
v___x_479_ = ((size_t)0ULL);
v_entries_480_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_477_, v___x_475_, v___f_476_, v_sz_478_, v___x_479_, v___x_475_);
lean_dec(v___x_475_);
v___x_481_ = lean_box(0);
v___x_482_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_483_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_483_, 0, v_inst_469_);
lean_closure_set(v___f_483_, 1, v_value_471_);
lean_closure_set(v___f_483_, 2, v___x_482_);
lean_closure_set(v___f_483_, 3, v___x_481_);
v_sz_484_ = lean_array_size(v_entries_480_);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_477_, v_entries_480_, v___f_483_, v_sz_484_, v___x_479_, v___x_482_);
v_fst_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_fst_486_);
lean_dec(v___x_485_);
if (lean_obj_tag(v_fst_486_) == 0)
{
uint8_t v___x_487_; 
v___x_487_ = 0;
return v___x_487_;
}
else
{
lean_object* v_val_488_; 
v_val_488_ = lean_ctor_get(v_fst_486_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v_fst_486_, 1);
if (lean_obj_tag(v_val_488_) == 0)
{
uint8_t v___x_489_; 
v___x_489_ = 0;
return v___x_489_;
}
else
{
lean_dec_ref_known(v_val_488_, 1);
return v___x_474_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_hasEntry_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_466_ = stack[2].m_obj;
lean_object* v_inst_467_ = stack[3].m_obj;
lean_object* v_map_468_ = stack[4].m_obj;
lean_object* v_inst_469_ = stack[5].m_obj;
lean_object* v_key_470_ = stack[6].m_obj;
lean_object* v_value_471_ = stack[7].m_obj;
uint8_t v_res_490_;
v_res_490_ = l_Std_Internal_IndexMultiMap_hasEntry(lean_box(0), lean_box(0), v_inst_466_, v_inst_467_, v_map_468_, v_inst_469_, v_key_470_, v_value_471_);
stack->m_num = v_res_490_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___boxed(lean_object* v_00_u03b1_491_, lean_object* v_00_u03b2_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_map_495_, lean_object* v_inst_496_, lean_object* v_key_497_, lean_object* v_value_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l_Std_Internal_IndexMultiMap_hasEntry(v_00_u03b1_491_, v_00_u03b2_492_, v_inst_493_, v_inst_494_, v_map_495_, v_inst_496_, v_key_497_, v_value_498_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f___redArg(lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_map_503_, lean_object* v_key_504_){
_start:
{
lean_object* v_entries_505_; lean_object* v_indexes_506_; uint8_t v___x_507_; 
v_entries_505_ = lean_ctor_get(v_map_503_, 0);
lean_inc_ref(v_entries_505_);
v_indexes_506_ = lean_ctor_get(v_map_503_, 1);
lean_inc_ref(v_indexes_506_);
lean_dec_ref(v_map_503_);
lean_inc(v_key_504_);
lean_inc_ref(v_inst_502_);
lean_inc_ref(v_inst_501_);
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_501_, v_inst_502_, v_indexes_506_, v_key_504_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec_ref(v_indexes_506_);
lean_dec_ref(v_entries_505_);
lean_dec(v_key_504_);
lean_dec_ref(v_inst_502_);
lean_dec_ref(v_inst_501_);
v___x_508_ = lean_box(0);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___f_510_; lean_object* v___x_511_; size_t v_sz_512_; size_t v___x_513_; lean_object* v_entries_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_501_, v_inst_502_, v_indexes_506_, v_key_504_);
lean_dec_ref(v_indexes_506_);
lean_inc_n(v___x_509_, 2);
v___f_510_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_510_, 0, v___x_509_);
lean_closure_set(v___f_510_, 1, v_entries_505_);
v___x_511_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_512_ = lean_array_size(v___x_509_);
v___x_513_ = ((size_t)0ULL);
v_entries_514_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_511_, v___x_509_, v___f_510_, v_sz_512_, v___x_513_, v___x_509_);
lean_dec(v___x_509_);
v___x_515_ = lean_array_get_size(v_entries_514_);
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_sub(v___x_515_, v___x_516_);
v___x_518_ = lean_nat_dec_lt(v___x_517_, v___x_515_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
lean_dec(v___x_517_);
lean_dec(v_entries_514_);
v___x_519_ = lean_box(0);
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_array_fget(v_entries_514_, v___x_517_);
lean_dec(v___x_517_);
lean_dec(v_entries_514_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f(lean_object* v_00_u03b1_522_, lean_object* v_00_u03b2_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_map_526_, lean_object* v_key_527_){
_start:
{
lean_object* v_entries_528_; lean_object* v_indexes_529_; uint8_t v___x_530_; 
v_entries_528_ = lean_ctor_get(v_map_526_, 0);
lean_inc_ref(v_entries_528_);
v_indexes_529_ = lean_ctor_get(v_map_526_, 1);
lean_inc_ref(v_indexes_529_);
lean_dec_ref(v_map_526_);
lean_inc(v_key_527_);
lean_inc_ref(v_inst_525_);
lean_inc_ref(v_inst_524_);
v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_524_, v_inst_525_, v_indexes_529_, v_key_527_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
lean_dec_ref(v_indexes_529_);
lean_dec_ref(v_entries_528_);
lean_dec(v_key_527_);
lean_dec_ref(v_inst_525_);
lean_dec_ref(v_inst_524_);
v___x_531_ = lean_box(0);
return v___x_531_;
}
else
{
lean_object* v___x_532_; lean_object* v___f_533_; lean_object* v___x_534_; size_t v_sz_535_; size_t v___x_536_; lean_object* v_entries_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_524_, v_inst_525_, v_indexes_529_, v_key_527_);
lean_dec_ref(v_indexes_529_);
lean_inc_n(v___x_532_, 2);
v___f_533_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_533_, 0, v___x_532_);
lean_closure_set(v___f_533_, 1, v_entries_528_);
v___x_534_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_535_ = lean_array_size(v___x_532_);
v___x_536_ = ((size_t)0ULL);
v_entries_537_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_534_, v___x_532_, v___f_533_, v_sz_535_, v___x_536_, v___x_532_);
lean_dec(v___x_532_);
v___x_538_ = lean_array_get_size(v_entries_537_);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_sub(v___x_538_, v___x_539_);
v___x_541_ = lean_nat_dec_lt(v___x_540_, v___x_538_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
lean_dec(v___x_540_);
lean_dec(v_entries_537_);
v___x_542_ = lean_box(0);
return v___x_542_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_array_fget(v_entries_537_, v___x_540_);
lean_dec(v___x_540_);
lean_dec(v_entries_537_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg(lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_map_547_, lean_object* v_key_548_, lean_object* v_d_549_){
_start:
{
lean_object* v_entries_550_; lean_object* v_indexes_551_; uint8_t v___x_552_; 
v_entries_550_ = lean_ctor_get(v_map_547_, 0);
v_indexes_551_ = lean_ctor_get(v_map_547_, 1);
lean_inc(v_key_548_);
lean_inc_ref(v_inst_546_);
lean_inc_ref(v_inst_545_);
v___x_552_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_545_, v_inst_546_, v_indexes_551_, v_key_548_);
if (v___x_552_ == 0)
{
lean_dec(v_key_548_);
lean_dec_ref(v_inst_546_);
lean_dec_ref(v_inst_545_);
lean_inc(v_d_549_);
return v_d_549_;
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v_entry_555_; lean_object* v___x_556_; lean_object* v_snd_557_; 
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_545_, v_inst_546_, v_indexes_551_, v_key_548_);
v___x_554_ = lean_unsigned_to_nat(0u);
v_entry_555_ = lean_array_fget(v___x_553_, v___x_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_array_fget_borrowed(v_entries_550_, v_entry_555_);
lean_dec(v_entry_555_);
v_snd_557_ = lean_ctor_get(v___x_556_, 1);
lean_inc(v_snd_557_);
return v_snd_557_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg___boxed(lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_map_560_, lean_object* v_key_561_, lean_object* v_d_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_Internal_IndexMultiMap_getD___redArg(v_inst_558_, v_inst_559_, v_map_560_, v_key_561_, v_d_562_);
lean_dec(v_d_562_);
lean_dec_ref(v_map_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD(lean_object* v_00_u03b1_564_, lean_object* v_00_u03b2_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_map_568_, lean_object* v_key_569_, lean_object* v_d_570_){
_start:
{
lean_object* v_entries_571_; lean_object* v_indexes_572_; uint8_t v___x_573_; 
v_entries_571_ = lean_ctor_get(v_map_568_, 0);
v_indexes_572_ = lean_ctor_get(v_map_568_, 1);
lean_inc(v_key_569_);
lean_inc_ref(v_inst_567_);
lean_inc_ref(v_inst_566_);
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_566_, v_inst_567_, v_indexes_572_, v_key_569_);
if (v___x_573_ == 0)
{
lean_dec(v_key_569_);
lean_dec_ref(v_inst_567_);
lean_dec_ref(v_inst_566_);
lean_inc(v_d_570_);
return v_d_570_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_entry_576_; lean_object* v___x_577_; lean_object* v_snd_578_; 
v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_566_, v_inst_567_, v_indexes_572_, v_key_569_);
v___x_575_ = lean_unsigned_to_nat(0u);
v_entry_576_ = lean_array_fget(v___x_574_, v___x_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_array_fget_borrowed(v_entries_571_, v_entry_576_);
lean_dec(v_entry_576_);
v_snd_578_ = lean_ctor_get(v___x_577_, 1);
lean_inc(v_snd_578_);
return v_snd_578_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___boxed(lean_object* v_00_u03b1_579_, lean_object* v_00_u03b2_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_map_583_, lean_object* v_key_584_, lean_object* v_d_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_Internal_IndexMultiMap_getD(v_00_u03b1_579_, v_00_u03b2_580_, v_inst_581_, v_inst_582_, v_map_583_, v_key_584_, v_d_585_);
lean_dec(v_d_585_);
lean_dec_ref(v_map_583_);
return v_res_586_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_590_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2));
v___x_591_ = lean_unsigned_to_nat(14u);
v___x_592_ = lean_unsigned_to_nat(22u);
v___x_593_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1));
v___x_594_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0));
v___x_595_ = l_mkPanicMessageWithDecl(v___x_594_, v___x_593_, v___x_592_, v___x_591_, v___x_590_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg(lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_map_599_, lean_object* v_key_600_){
_start:
{
lean_object* v_entries_601_; lean_object* v_indexes_602_; uint8_t v___x_603_; 
v_entries_601_ = lean_ctor_get(v_map_599_, 0);
v_indexes_602_ = lean_ctor_get(v_map_599_, 1);
lean_inc(v_key_600_);
lean_inc_ref(v_inst_597_);
lean_inc_ref(v_inst_596_);
v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_596_, v_inst_597_, v_indexes_602_, v_key_600_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec(v_key_600_);
lean_dec_ref(v_inst_597_);
lean_dec_ref(v_inst_596_);
v___x_604_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_605_ = l_panic___redArg(v_inst_598_, v___x_604_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_entry_608_; lean_object* v___x_609_; lean_object* v_snd_610_; 
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_596_, v_inst_597_, v_indexes_602_, v_key_600_);
v___x_607_ = lean_unsigned_to_nat(0u);
v_entry_608_ = lean_array_fget(v___x_606_, v___x_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_array_fget_borrowed(v_entries_601_, v_entry_608_);
lean_dec(v_entry_608_);
v_snd_610_ = lean_ctor_get(v___x_609_, 1);
lean_inc(v_snd_610_);
return v_snd_610_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___boxed(lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_map_614_, lean_object* v_key_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_Internal_IndexMultiMap_get_x21___redArg(v_inst_611_, v_inst_612_, v_inst_613_, v_map_614_, v_key_615_);
lean_dec_ref(v_map_614_);
lean_dec(v_inst_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_map_622_, lean_object* v_key_623_){
_start:
{
lean_object* v_entries_624_; lean_object* v_indexes_625_; uint8_t v___x_626_; 
v_entries_624_ = lean_ctor_get(v_map_622_, 0);
v_indexes_625_ = lean_ctor_get(v_map_622_, 1);
lean_inc(v_key_623_);
lean_inc_ref(v_inst_620_);
lean_inc_ref(v_inst_619_);
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_619_, v_inst_620_, v_indexes_625_, v_key_623_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v_key_623_);
lean_dec_ref(v_inst_620_);
lean_dec_ref(v_inst_619_);
v___x_627_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_628_ = l_panic___redArg(v_inst_621_, v___x_627_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_entry_631_; lean_object* v___x_632_; lean_object* v_snd_633_; 
v___x_629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_619_, v_inst_620_, v_indexes_625_, v_key_623_);
v___x_630_ = lean_unsigned_to_nat(0u);
v_entry_631_ = lean_array_fget(v___x_629_, v___x_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_array_fget_borrowed(v_entries_624_, v_entry_631_);
lean_dec(v_entry_631_);
v_snd_633_ = lean_ctor_get(v___x_632_, 1);
lean_inc(v_snd_633_);
return v_snd_633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___boxed(lean_object* v_00_u03b1_634_, lean_object* v_00_u03b2_635_, lean_object* v_inst_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_map_639_, lean_object* v_key_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_Internal_IndexMultiMap_get_x21(v_00_u03b1_634_, v_00_u03b2_635_, v_inst_636_, v_inst_637_, v_inst_638_, v_map_639_, v_key_640_);
lean_dec_ref(v_map_639_);
lean_dec(v_inst_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter___redArg(lean_object* v_x_642_, lean_object* v_h__1_643_, lean_object* v_h__2_644_){
_start:
{
if (lean_obj_tag(v_x_642_) == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v_h__1_643_);
v___x_645_ = lean_box(0);
v___x_646_ = lean_apply_1(v_h__2_644_, v___x_645_);
return v___x_646_;
}
else
{
lean_object* v_val_647_; lean_object* v___x_648_; 
lean_dec(v_h__2_644_);
v_val_647_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v_x_642_, 1);
v___x_648_ = lean_apply_1(v_h__1_643_, v_val_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter(lean_object* v_motive_649_, lean_object* v_x_650_, lean_object* v_h__1_651_, lean_object* v_h__2_652_){
_start:
{
if (lean_obj_tag(v_x_650_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec(v_h__1_651_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_apply_1(v_h__2_652_, v___x_653_);
return v___x_654_;
}
else
{
lean_object* v_val_655_; lean_object* v___x_656_; 
lean_dec(v_h__2_652_);
v_val_655_ = lean_ctor_get(v_x_650_, 0);
lean_inc(v_val_655_);
lean_dec_ref_known(v_x_650_, 1);
v___x_656_ = lean_apply_1(v_h__1_651_, v_val_655_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(lean_object* v_i_657_, lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_mk_empty_array_with_capacity(v___x_659_);
v___x_661_ = lean_array_push(v___x_660_, v_i_657_);
v___x_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
else
{
lean_object* v_val_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_val_663_ = lean_ctor_get(v_x_658_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_671_ == 0)
{
v___x_665_ = v_x_658_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_val_663_);
lean_dec(v_x_658_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = lean_array_push(v_val_663_, v_i_657_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg(lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_map_674_, lean_object* v_key_675_, lean_object* v_value_676_){
_start:
{
lean_object* v_entries_677_; lean_object* v_indexes_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_690_; 
v_entries_677_ = lean_ctor_get(v_map_674_, 0);
v_indexes_678_ = lean_ctor_get(v_map_674_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v_map_674_);
if (v_isSharedCheck_690_ == 0)
{
v___x_680_ = v_map_674_;
v_isShared_681_ = v_isSharedCheck_690_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_indexes_678_);
lean_inc(v_entries_677_);
lean_dec(v_map_674_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_690_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_i_682_; lean_object* v_f_683_; lean_object* v___x_684_; lean_object* v_entries_685_; lean_object* v_indexes_686_; lean_object* v___x_688_; 
v_i_682_ = lean_array_get_size(v_entries_677_);
v_f_683_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_683_, 0, v_i_682_);
lean_inc(v_key_675_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_key_675_);
lean_ctor_set(v___x_684_, 1, v_value_676_);
v_entries_685_ = lean_array_push(v_entries_677_, v___x_684_);
v_indexes_686_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_672_, v_inst_673_, v_indexes_678_, v_key_675_, v_f_683_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v_indexes_686_);
lean_ctor_set(v___x_680_, 0, v_entries_685_);
v___x_688_ = v___x_680_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_entries_685_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_indexes_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert(lean_object* v_00_u03b1_691_, lean_object* v_00_u03b2_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_map_697_, lean_object* v_key_698_, lean_object* v_value_699_){
_start:
{
lean_object* v_entries_700_; lean_object* v_indexes_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_713_; 
v_entries_700_ = lean_ctor_get(v_map_697_, 0);
v_indexes_701_ = lean_ctor_get(v_map_697_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_map_697_);
if (v_isSharedCheck_713_ == 0)
{
v___x_703_ = v_map_697_;
v_isShared_704_ = v_isSharedCheck_713_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_indexes_701_);
lean_inc(v_entries_700_);
lean_dec(v_map_697_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_713_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_i_705_; lean_object* v_f_706_; lean_object* v___x_707_; lean_object* v_entries_708_; lean_object* v_indexes_709_; lean_object* v___x_711_; 
v_i_705_ = lean_array_get_size(v_entries_700_);
v_f_706_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_706_, 0, v_i_705_);
lean_inc(v_key_698_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v_key_698_);
lean_ctor_set(v___x_707_, 1, v_value_699_);
v_entries_708_ = lean_array_push(v_entries_700_, v___x_707_);
v_indexes_709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_693_, v_inst_694_, v_indexes_701_, v_key_698_, v_f_706_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v_indexes_709_);
lean_ctor_set(v___x_703_, 0, v_entries_708_);
v___x_711_ = v___x_703_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_entries_708_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_indexes_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1(lean_object* v_key_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_x1_717_, lean_object* v_x2_718_){
_start:
{
lean_object* v_entries_719_; lean_object* v_indexes_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_732_; 
v_entries_719_ = lean_ctor_get(v_x1_717_, 0);
v_indexes_720_ = lean_ctor_get(v_x1_717_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_x1_717_);
if (v_isSharedCheck_732_ == 0)
{
v___x_722_ = v_x1_717_;
v_isShared_723_ = v_isSharedCheck_732_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_indexes_720_);
lean_inc(v_entries_719_);
lean_dec(v_x1_717_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_732_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_i_724_; lean_object* v_f_725_; lean_object* v___x_726_; lean_object* v_entries_727_; lean_object* v_indexes_728_; lean_object* v___x_730_; 
v_i_724_ = lean_array_get_size(v_entries_719_);
v_f_725_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_725_, 0, v_i_724_);
lean_inc(v_key_714_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_key_714_);
lean_ctor_set(v___x_726_, 1, v_x2_718_);
v_entries_727_ = lean_array_push(v_entries_719_, v___x_726_);
v_indexes_728_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_715_, v_inst_716_, v_indexes_720_, v_key_714_, v_f_725_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v_indexes_728_);
lean_ctor_set(v___x_722_, 0, v_entries_727_);
v___x_730_ = v___x_722_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_entries_727_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_indexes_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg(lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_map_735_, lean_object* v_key_736_, lean_object* v_values_737_){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_array_get_size(v_values_737_);
v___x_740_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_741_ = lean_nat_dec_lt(v___x_738_, v___x_739_);
if (v___x_741_ == 0)
{
lean_dec_ref(v_values_737_);
lean_dec(v_key_736_);
lean_dec_ref(v_inst_734_);
lean_dec_ref(v_inst_733_);
return v_map_735_;
}
else
{
lean_object* v___f_742_; uint8_t v___x_743_; 
v___f_742_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_742_, 0, v_key_736_);
lean_closure_set(v___f_742_, 1, v_inst_733_);
lean_closure_set(v___f_742_, 2, v_inst_734_);
v___x_743_ = lean_nat_dec_le(v___x_739_, v___x_739_);
if (v___x_743_ == 0)
{
if (v___x_741_ == 0)
{
lean_dec_ref(v___f_742_);
lean_dec_ref(v_values_737_);
return v_map_735_;
}
else
{
size_t v___x_744_; size_t v___x_745_; lean_object* v___x_746_; 
v___x_744_ = ((size_t)0ULL);
v___x_745_ = lean_usize_of_nat(v___x_739_);
v___x_746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_740_, v___f_742_, v_values_737_, v___x_744_, v___x_745_, v_map_735_);
return v___x_746_;
}
}
else
{
size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_747_ = ((size_t)0ULL);
v___x_748_ = lean_usize_of_nat(v___x_739_);
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_740_, v___f_742_, v_values_737_, v___x_747_, v___x_748_, v_map_735_);
return v___x_749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany(lean_object* v_00_u03b1_750_, lean_object* v_00_u03b2_751_, lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_map_756_, lean_object* v_key_757_, lean_object* v_values_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = lean_array_get_size(v_values_758_);
v___x_761_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_762_ = lean_nat_dec_lt(v___x_759_, v___x_760_);
if (v___x_762_ == 0)
{
lean_dec_ref(v_values_758_);
lean_dec(v_key_757_);
lean_dec_ref(v_inst_753_);
lean_dec_ref(v_inst_752_);
return v_map_756_;
}
else
{
lean_object* v___f_763_; uint8_t v___x_764_; 
v___f_763_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_763_, 0, v_key_757_);
lean_closure_set(v___f_763_, 1, v_inst_752_);
lean_closure_set(v___f_763_, 2, v_inst_753_);
v___x_764_ = lean_nat_dec_le(v___x_760_, v___x_760_);
if (v___x_764_ == 0)
{
if (v___x_762_ == 0)
{
lean_dec_ref(v___f_763_);
lean_dec_ref(v_values_758_);
return v_map_756_;
}
else
{
size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v___x_765_ = ((size_t)0ULL);
v___x_766_ = lean_usize_of_nat(v___x_760_);
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_761_, v___f_763_, v_values_758_, v___x_765_, v___x_766_, v_map_756_);
return v___x_767_;
}
}
else
{
size_t v___x_768_; size_t v___x_769_; lean_object* v___x_770_; 
v___x_768_ = ((size_t)0ULL);
v___x_769_ = lean_usize_of_nat(v___x_760_);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_761_, v___f_763_, v_values_758_, v___x_768_, v___x_769_, v_map_756_);
return v___x_770_;
}
}
}
}
lean_object* l_Std_Internal_IndexMultiMap_empty___redArg(){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3);
return v___x_772_;
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_773_;
v_res_773_ = l_Std_Internal_IndexMultiMap_empty___redArg();
stack->m_obj
 = v_res_773_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___redArg___boxed(lean_object* v___dummy_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_Internal_IndexMultiMap_empty___redArg();
return v_res_775_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___closed__0(void){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_Internal_IndexMultiMap_empty___redArg();
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object* v_00_u03b1_777_, lean_object* v_00_u03b2_778_, lean_object* v_inst_779_, lean_object* v_inst_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___boxed(lean_object* v_00_u03b1_782_, lean_object* v_00_u03b2_783_, lean_object* v_inst_784_, lean_object* v_inst_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_Internal_IndexMultiMap_empty(v_00_u03b1_782_, v_00_u03b2_783_, v_inst_784_, v_inst_785_);
lean_dec_ref(v_inst_785_);
lean_dec_ref(v_inst_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1(lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_acc_789_, lean_object* v_x_790_){
_start:
{
lean_object* v_fst_791_; lean_object* v_entries_792_; lean_object* v_indexes_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_804_; 
v_fst_791_ = lean_ctor_get(v_x_790_, 0);
lean_inc(v_fst_791_);
v_entries_792_ = lean_ctor_get(v_acc_789_, 0);
v_indexes_793_ = lean_ctor_get(v_acc_789_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_acc_789_);
if (v_isSharedCheck_804_ == 0)
{
v___x_795_ = v_acc_789_;
v_isShared_796_ = v_isSharedCheck_804_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_indexes_793_);
lean_inc(v_entries_792_);
lean_dec(v_acc_789_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_804_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_i_797_; lean_object* v_f_798_; lean_object* v_entries_799_; lean_object* v_indexes_800_; lean_object* v___x_802_; 
v_i_797_ = lean_array_get_size(v_entries_792_);
v_f_798_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_798_, 0, v_i_797_);
v_entries_799_ = lean_array_push(v_entries_792_, v_x_790_);
v_indexes_800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_787_, v_inst_788_, v_indexes_793_, v_fst_791_, v_f_798_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v_indexes_800_);
lean_ctor_set(v___x_795_, 0, v_entries_799_);
v___x_802_ = v___x_795_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_entries_799_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_indexes_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg(lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_pairs_807_){
_start:
{
lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___f_808_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_808_, 0, v_inst_805_);
lean_closure_set(v___f_808_, 1, v_inst_806_);
v___x_809_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_810_ = l_List_foldl___redArg(v___f_808_, v___x_809_, v_pairs_807_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList(lean_object* v_00_u03b1_811_, lean_object* v_00_u03b2_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_pairs_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Std_Internal_IndexMultiMap_ofList___redArg(v_inst_813_, v_inst_814_, v_pairs_817_);
return v___x_818_;
}
}
uint8_t l_Std_Internal_IndexMultiMap_contains___redArg(lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_map_821_, lean_object* v_key_822_){
_start:
{
lean_object* v_indexes_823_; uint8_t v___x_824_; 
v_indexes_823_ = lean_ctor_get(v_map_821_, 1);
v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_819_, v_inst_820_, v_indexes_823_, v_key_822_);
return v___x_824_;
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_819_ = stack[0].m_obj;
lean_object* v_inst_820_ = stack[1].m_obj;
lean_object* v_map_821_ = stack[2].m_obj;
lean_object* v_key_822_ = stack[3].m_obj;
uint8_t v_res_825_;
v_res_825_ = l_Std_Internal_IndexMultiMap_contains___redArg(v_inst_819_, v_inst_820_, v_map_821_, v_key_822_);
stack->m_num = v_res_825_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___redArg___boxed(lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_map_828_, lean_object* v_key_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_Std_Internal_IndexMultiMap_contains___redArg(v_inst_826_, v_inst_827_, v_map_828_, v_key_829_);
lean_dec_ref(v_map_828_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
uint8_t l_Std_Internal_IndexMultiMap_contains(lean_object* v_00_u03b1_832_, lean_object* v_00_u03b2_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_map_836_, lean_object* v_key_837_){
_start:
{
lean_object* v_indexes_838_; uint8_t v___x_839_; 
v_indexes_838_ = lean_ctor_get(v_map_836_, 1);
v___x_839_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_834_, v_inst_835_, v_indexes_838_, v_key_837_);
return v___x_839_;
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_834_ = stack[2].m_obj;
lean_object* v_inst_835_ = stack[3].m_obj;
lean_object* v_map_836_ = stack[4].m_obj;
lean_object* v_key_837_ = stack[5].m_obj;
uint8_t v_res_840_;
v_res_840_ = l_Std_Internal_IndexMultiMap_contains(lean_box(0), lean_box(0), v_inst_834_, v_inst_835_, v_map_836_, v_key_837_);
stack->m_num = v_res_840_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___boxed(lean_object* v_00_u03b1_841_, lean_object* v_00_u03b2_842_, lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_map_845_, lean_object* v_key_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Std_Internal_IndexMultiMap_contains(v_00_u03b1_841_, v_00_u03b2_842_, v_inst_843_, v_inst_844_, v_map_845_, v_key_846_);
lean_dec_ref(v_map_845_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg___lam__1(lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_key_851_, lean_object* v_f_852_, lean_object* v_x1_853_, lean_object* v_x2_854_){
_start:
{
lean_object* v_fst_855_; lean_object* v_snd_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_881_; 
v_fst_855_ = lean_ctor_get(v_x2_854_, 0);
v_snd_856_ = lean_ctor_get(v_x2_854_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v_x2_854_);
if (v_isSharedCheck_881_ == 0)
{
v___x_858_ = v_x2_854_;
v_isShared_859_ = v_isSharedCheck_881_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_snd_856_);
lean_inc(v_fst_855_);
lean_dec(v_x2_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_881_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___y_861_; lean_object* v___x_878_; uint8_t v___x_879_; 
lean_inc_ref(v_inst_849_);
lean_inc(v_fst_855_);
v___x_878_ = lean_apply_2(v_inst_849_, v_fst_855_, v_key_851_);
v___x_879_ = lean_unbox(v___x_878_);
if (v___x_879_ == 0)
{
lean_dec(v_f_852_);
v___y_861_ = v_snd_856_;
goto v___jp_860_;
}
else
{
lean_object* v___x_880_; 
v___x_880_ = lean_apply_1(v_f_852_, v_snd_856_);
v___y_861_ = v___x_880_;
goto v___jp_860_;
}
v___jp_860_:
{
lean_object* v_entries_862_; lean_object* v_indexes_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_877_; 
v_entries_862_ = lean_ctor_get(v_x1_853_, 0);
v_indexes_863_ = lean_ctor_get(v_x1_853_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_x1_853_);
if (v_isSharedCheck_877_ == 0)
{
v___x_865_ = v_x1_853_;
v_isShared_866_ = v_isSharedCheck_877_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_indexes_863_);
lean_inc(v_entries_862_);
lean_dec(v_x1_853_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_877_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_i_867_; lean_object* v_f_868_; lean_object* v___x_870_; 
v_i_867_ = lean_array_get_size(v_entries_862_);
v_f_868_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_868_, 0, v_i_867_);
lean_inc(v_fst_855_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 1, v___y_861_);
v___x_870_ = v___x_858_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_fst_855_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___y_861_);
v___x_870_ = v_reuseFailAlloc_876_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v_entries_871_; lean_object* v_indexes_872_; lean_object* v___x_874_; 
v_entries_871_ = lean_array_push(v_entries_862_, v___x_870_);
v_indexes_872_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_849_, v_inst_850_, v_indexes_863_, v_fst_855_, v_f_868_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 1, v_indexes_872_);
lean_ctor_set(v___x_865_, 0, v_entries_871_);
v___x_874_ = v___x_865_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_entries_871_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_indexes_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg(lean_object* v_inst_882_, lean_object* v_inst_883_, lean_object* v_map_884_, lean_object* v_key_885_, lean_object* v_f_886_){
_start:
{
uint8_t v___x_887_; 
lean_inc(v_key_885_);
lean_inc_ref(v_inst_883_);
lean_inc_ref(v_inst_882_);
v___x_887_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_882_, v_inst_883_, v_key_885_, v_map_884_);
if (v___x_887_ == 0)
{
lean_dec(v_f_886_);
lean_dec(v_key_885_);
lean_dec_ref(v_inst_883_);
lean_dec_ref(v_inst_882_);
return v_map_884_;
}
else
{
lean_object* v_entries_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v_entries_888_ = lean_ctor_get(v_map_884_, 0);
lean_inc_ref(v_entries_888_);
lean_dec_ref(v_map_884_);
v___x_889_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_890_ = lean_unsigned_to_nat(0u);
v___x_891_ = lean_array_get_size(v_entries_888_);
v___x_892_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_893_ = lean_nat_dec_lt(v___x_890_, v___x_891_);
if (v___x_893_ == 0)
{
lean_dec_ref(v_entries_888_);
lean_dec(v_f_886_);
lean_dec(v_key_885_);
lean_dec_ref(v_inst_883_);
lean_dec_ref(v_inst_882_);
return v___x_889_;
}
else
{
lean_object* v___f_894_; uint8_t v___x_895_; 
v___f_894_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_894_, 0, v_inst_882_);
lean_closure_set(v___f_894_, 1, v_inst_883_);
lean_closure_set(v___f_894_, 2, v_key_885_);
lean_closure_set(v___f_894_, 3, v_f_886_);
v___x_895_ = lean_nat_dec_le(v___x_891_, v___x_891_);
if (v___x_895_ == 0)
{
if (v___x_893_ == 0)
{
lean_dec_ref(v___f_894_);
lean_dec_ref(v_entries_888_);
return v___x_889_;
}
else
{
size_t v___x_896_; size_t v___x_897_; lean_object* v___x_898_; 
v___x_896_ = ((size_t)0ULL);
v___x_897_ = lean_usize_of_nat(v___x_891_);
v___x_898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_892_, v___f_894_, v_entries_888_, v___x_896_, v___x_897_, v___x_889_);
return v___x_898_;
}
}
else
{
size_t v___x_899_; size_t v___x_900_; lean_object* v___x_901_; 
v___x_899_ = ((size_t)0ULL);
v___x_900_ = lean_usize_of_nat(v___x_891_);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_892_, v___f_894_, v_entries_888_, v___x_899_, v___x_900_, v___x_889_);
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v_map_908_, lean_object* v_key_909_, lean_object* v_f_910_){
_start:
{
uint8_t v___x_911_; 
lean_inc(v_key_909_);
lean_inc_ref(v_inst_905_);
lean_inc_ref(v_inst_904_);
v___x_911_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_904_, v_inst_905_, v_key_909_, v_map_908_);
if (v___x_911_ == 0)
{
lean_dec(v_f_910_);
lean_dec(v_key_909_);
lean_dec_ref(v_inst_905_);
lean_dec_ref(v_inst_904_);
return v_map_908_;
}
else
{
lean_object* v_entries_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_entries_912_ = lean_ctor_get(v_map_908_, 0);
lean_inc_ref(v_entries_912_);
lean_dec_ref(v_map_908_);
v___x_913_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = lean_array_get_size(v_entries_912_);
v___x_916_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_917_ = lean_nat_dec_lt(v___x_914_, v___x_915_);
if (v___x_917_ == 0)
{
lean_dec_ref(v_entries_912_);
lean_dec(v_f_910_);
lean_dec(v_key_909_);
lean_dec_ref(v_inst_905_);
lean_dec_ref(v_inst_904_);
return v___x_913_;
}
else
{
lean_object* v___f_918_; uint8_t v___x_919_; 
v___f_918_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_918_, 0, v_inst_904_);
lean_closure_set(v___f_918_, 1, v_inst_905_);
lean_closure_set(v___f_918_, 2, v_key_909_);
lean_closure_set(v___f_918_, 3, v_f_910_);
v___x_919_ = lean_nat_dec_le(v___x_915_, v___x_915_);
if (v___x_919_ == 0)
{
if (v___x_917_ == 0)
{
lean_dec_ref(v___f_918_);
lean_dec_ref(v_entries_912_);
return v___x_913_;
}
else
{
size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; 
v___x_920_ = ((size_t)0ULL);
v___x_921_ = lean_usize_of_nat(v___x_915_);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_916_, v___f_918_, v_entries_912_, v___x_920_, v___x_921_, v___x_913_);
return v___x_922_;
}
}
else
{
size_t v___x_923_; size_t v___x_924_; lean_object* v___x_925_; 
v___x_923_ = ((size_t)0ULL);
v___x_924_ = lean_usize_of_nat(v___x_915_);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_916_, v___f_918_, v_entries_912_, v___x_923_, v___x_924_, v___x_913_);
return v___x_925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast___redArg(lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_map_928_, lean_object* v_key_929_, lean_object* v_value_930_){
_start:
{
lean_object* v_entries_931_; lean_object* v_indexes_932_; uint8_t v___x_933_; 
v_entries_931_ = lean_ctor_get(v_map_928_, 0);
v_indexes_932_ = lean_ctor_get(v_map_928_, 1);
lean_inc(v_key_929_);
lean_inc_ref(v_inst_927_);
lean_inc_ref(v_inst_926_);
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_926_, v_inst_927_, v_indexes_932_, v_key_929_);
if (v___x_933_ == 0)
{
lean_dec(v_value_930_);
lean_dec(v_key_929_);
lean_dec_ref(v_inst_927_);
lean_dec_ref(v_inst_926_);
return v_map_928_;
}
else
{
lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_947_; 
lean_inc_ref(v_indexes_932_);
lean_inc_ref(v_entries_931_);
v_isSharedCheck_947_ = !lean_is_exclusive(v_map_928_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; lean_object* v_unused_949_; 
v_unused_948_ = lean_ctor_get(v_map_928_, 1);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_map_928_, 0);
lean_dec(v_unused_949_);
v___x_935_ = v_map_928_;
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
else
{
lean_dec(v_map_928_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_idxs_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_lastIdx_941_; lean_object* v___x_942_; lean_object* v_entries_943_; lean_object* v___x_945_; 
lean_inc(v_key_929_);
v_idxs_937_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_926_, v_inst_927_, v_indexes_932_, v_key_929_);
v___x_938_ = lean_array_get_size(v_idxs_937_);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_sub(v___x_938_, v___x_939_);
v_lastIdx_941_ = lean_array_fget(v_idxs_937_, v___x_940_);
lean_dec(v___x_940_);
lean_dec(v_idxs_937_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v_key_929_);
lean_ctor_set(v___x_942_, 1, v_value_930_);
v_entries_943_ = lean_array_fset(v_entries_931_, v_lastIdx_941_, v___x_942_);
lean_dec(v_lastIdx_941_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v_entries_943_);
v___x_945_ = v___x_935_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_entries_943_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_indexes_932_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast(lean_object* v_00_u03b1_950_, lean_object* v_00_u03b2_951_, lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v_map_954_, lean_object* v_key_955_, lean_object* v_value_956_){
_start:
{
lean_object* v_entries_957_; lean_object* v_indexes_958_; uint8_t v___x_959_; 
v_entries_957_ = lean_ctor_get(v_map_954_, 0);
v_indexes_958_ = lean_ctor_get(v_map_954_, 1);
lean_inc(v_key_955_);
lean_inc_ref(v_inst_953_);
lean_inc_ref(v_inst_952_);
v___x_959_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_952_, v_inst_953_, v_indexes_958_, v_key_955_);
if (v___x_959_ == 0)
{
lean_dec(v_value_956_);
lean_dec(v_key_955_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_952_);
return v_map_954_;
}
else
{
lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_973_; 
lean_inc_ref(v_indexes_958_);
lean_inc_ref(v_entries_957_);
v_isSharedCheck_973_ = !lean_is_exclusive(v_map_954_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; lean_object* v_unused_975_; 
v_unused_974_ = lean_ctor_get(v_map_954_, 1);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_map_954_, 0);
lean_dec(v_unused_975_);
v___x_961_ = v_map_954_;
v_isShared_962_ = v_isSharedCheck_973_;
goto v_resetjp_960_;
}
else
{
lean_dec(v_map_954_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_973_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_idxs_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_lastIdx_967_; lean_object* v___x_968_; lean_object* v_entries_969_; lean_object* v___x_971_; 
lean_inc(v_key_955_);
v_idxs_963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_952_, v_inst_953_, v_indexes_958_, v_key_955_);
v___x_964_ = lean_array_get_size(v_idxs_963_);
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_nat_sub(v___x_964_, v___x_965_);
v_lastIdx_967_ = lean_array_fget(v_idxs_963_, v___x_966_);
lean_dec(v___x_966_);
lean_dec(v_idxs_963_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v_key_955_);
lean_ctor_set(v___x_968_, 1, v_value_956_);
v_entries_969_ = lean_array_fset(v_entries_957_, v_lastIdx_967_, v___x_968_);
lean_dec(v_lastIdx_967_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v_entries_969_);
v___x_971_ = v___x_961_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_entries_969_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_indexes_958_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(lean_object* v_inst_976_, lean_object* v_key_977_, lean_object* v_inst_978_, lean_object* v_x1_979_, lean_object* v_x2_980_){
_start:
{
lean_object* v_fst_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_fst_981_ = lean_ctor_get(v_x2_980_, 0);
lean_inc_n(v_fst_981_, 2);
lean_inc_ref(v_inst_976_);
v___x_982_ = lean_apply_2(v_inst_976_, v_key_977_, v_fst_981_);
v___x_983_ = lean_unbox(v___x_982_);
if (v___x_983_ == 0)
{
lean_object* v_entries_984_; lean_object* v_indexes_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_996_; 
v_entries_984_ = lean_ctor_get(v_x1_979_, 0);
v_indexes_985_ = lean_ctor_get(v_x1_979_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v_x1_979_);
if (v_isSharedCheck_996_ == 0)
{
v___x_987_ = v_x1_979_;
v_isShared_988_ = v_isSharedCheck_996_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_indexes_985_);
lean_inc(v_entries_984_);
lean_dec(v_x1_979_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_996_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_i_989_; lean_object* v_f_990_; lean_object* v_entries_991_; lean_object* v_indexes_992_; lean_object* v___x_994_; 
v_i_989_ = lean_array_get_size(v_entries_984_);
v_f_990_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_990_, 0, v_i_989_);
v_entries_991_ = lean_array_push(v_entries_984_, v_x2_980_);
v_indexes_992_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_976_, v_inst_978_, v_indexes_985_, v_fst_981_, v_f_990_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_indexes_992_);
lean_ctor_set(v___x_987_, 0, v_entries_991_);
v___x_994_ = v___x_987_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_entries_991_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_indexes_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
else
{
lean_dec(v_fst_981_);
lean_dec_ref(v_x2_980_);
lean_dec_ref(v_inst_978_);
lean_dec_ref(v_inst_976_);
return v_x1_979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg(lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_map_999_, lean_object* v_key_1000_){
_start:
{
uint8_t v___x_1001_; 
lean_inc(v_key_1000_);
lean_inc_ref(v_inst_998_);
lean_inc_ref(v_inst_997_);
v___x_1001_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_997_, v_inst_998_, v_key_1000_, v_map_999_);
if (v___x_1001_ == 0)
{
lean_dec(v_key_1000_);
lean_dec_ref(v_inst_998_);
lean_dec_ref(v_inst_997_);
return v_map_999_;
}
else
{
lean_object* v_entries_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_entries_1002_ = lean_ctor_get(v_map_999_, 0);
lean_inc_ref(v_entries_1002_);
lean_dec_ref(v_map_999_);
v___x_1003_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_array_get_size(v_entries_1002_);
v___x_1006_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1007_ = lean_nat_dec_lt(v___x_1004_, v___x_1005_);
if (v___x_1007_ == 0)
{
lean_dec_ref(v_entries_1002_);
lean_dec(v_key_1000_);
lean_dec_ref(v_inst_998_);
lean_dec_ref(v_inst_997_);
return v___x_1003_;
}
else
{
lean_object* v___f_1008_; uint8_t v___x_1009_; 
v___f_1008_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1008_, 0, v_inst_997_);
lean_closure_set(v___f_1008_, 1, v_key_1000_);
lean_closure_set(v___f_1008_, 2, v_inst_998_);
v___x_1009_ = lean_nat_dec_le(v___x_1005_, v___x_1005_);
if (v___x_1009_ == 0)
{
if (v___x_1007_ == 0)
{
lean_dec_ref(v___f_1008_);
lean_dec_ref(v_entries_1002_);
return v___x_1003_;
}
else
{
size_t v___x_1010_; size_t v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = ((size_t)0ULL);
v___x_1011_ = lean_usize_of_nat(v___x_1005_);
v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1006_, v___f_1008_, v_entries_1002_, v___x_1010_, v___x_1011_, v___x_1003_);
return v___x_1012_;
}
}
else
{
size_t v___x_1013_; size_t v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = ((size_t)0ULL);
v___x_1014_ = lean_usize_of_nat(v___x_1005_);
v___x_1015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1006_, v___f_1008_, v_entries_1002_, v___x_1013_, v___x_1014_, v___x_1003_);
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03b2_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_map_1022_, lean_object* v_key_1023_){
_start:
{
uint8_t v___x_1024_; 
lean_inc(v_key_1023_);
lean_inc_ref(v_inst_1019_);
lean_inc_ref(v_inst_1018_);
v___x_1024_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_1018_, v_inst_1019_, v_key_1023_, v_map_1022_);
if (v___x_1024_ == 0)
{
lean_dec(v_key_1023_);
lean_dec_ref(v_inst_1019_);
lean_dec_ref(v_inst_1018_);
return v_map_1022_;
}
else
{
lean_object* v_entries_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v_entries_1025_ = lean_ctor_get(v_map_1022_, 0);
lean_inc_ref(v_entries_1025_);
lean_dec_ref(v_map_1022_);
v___x_1026_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = lean_array_get_size(v_entries_1025_);
v___x_1029_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1030_ = lean_nat_dec_lt(v___x_1027_, v___x_1028_);
if (v___x_1030_ == 0)
{
lean_dec_ref(v_entries_1025_);
lean_dec(v_key_1023_);
lean_dec_ref(v_inst_1019_);
lean_dec_ref(v_inst_1018_);
return v___x_1026_;
}
else
{
lean_object* v___f_1031_; uint8_t v___x_1032_; 
v___f_1031_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1031_, 0, v_inst_1018_);
lean_closure_set(v___f_1031_, 1, v_key_1023_);
lean_closure_set(v___f_1031_, 2, v_inst_1019_);
v___x_1032_ = lean_nat_dec_le(v___x_1028_, v___x_1028_);
if (v___x_1032_ == 0)
{
if (v___x_1030_ == 0)
{
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_entries_1025_);
return v___x_1026_;
}
else
{
size_t v___x_1033_; size_t v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = ((size_t)0ULL);
v___x_1034_ = lean_usize_of_nat(v___x_1028_);
v___x_1035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1029_, v___f_1031_, v_entries_1025_, v___x_1033_, v___x_1034_, v___x_1026_);
return v___x_1035_;
}
}
else
{
size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = lean_usize_of_nat(v___x_1028_);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1029_, v___f_1031_, v_entries_1025_, v___x_1036_, v___x_1037_, v___x_1026_);
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1(lean_object* v_inst_1039_, lean_object* v_keys_1040_, lean_object* v_inst_1041_, lean_object* v_x1_1042_, lean_object* v_x2_1043_){
_start:
{
lean_object* v_fst_1044_; uint8_t v___x_1045_; 
v_fst_1044_ = lean_ctor_get(v_x2_1043_, 0);
lean_inc_n(v_fst_1044_, 2);
lean_inc_ref(v_inst_1039_);
v___x_1045_ = l_Array_contains___redArg(v_inst_1039_, v_keys_1040_, v_fst_1044_);
if (v___x_1045_ == 0)
{
lean_object* v_entries_1046_; lean_object* v_indexes_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1058_; 
v_entries_1046_ = lean_ctor_get(v_x1_1042_, 0);
v_indexes_1047_ = lean_ctor_get(v_x1_1042_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_x1_1042_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1049_ = v_x1_1042_;
v_isShared_1050_ = v_isSharedCheck_1058_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_indexes_1047_);
lean_inc(v_entries_1046_);
lean_dec(v_x1_1042_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1058_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v_i_1051_; lean_object* v_f_1052_; lean_object* v_entries_1053_; lean_object* v_indexes_1054_; lean_object* v___x_1056_; 
v_i_1051_ = lean_array_get_size(v_entries_1046_);
v_f_1052_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1052_, 0, v_i_1051_);
v_entries_1053_ = lean_array_push(v_entries_1046_, v_x2_1043_);
v_indexes_1054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1039_, v_inst_1041_, v_indexes_1047_, v_fst_1044_, v_f_1052_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v_indexes_1054_);
lean_ctor_set(v___x_1049_, 0, v_entries_1053_);
v___x_1056_ = v___x_1049_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_entries_1053_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_indexes_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
else
{
lean_dec(v_fst_1044_);
lean_dec_ref(v_x2_1043_);
lean_dec_ref(v_inst_1041_);
lean_dec_ref(v_inst_1039_);
return v_x1_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany___redArg(lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_map_1061_, lean_object* v_keys_1062_){
_start:
{
lean_object* v_entries_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v_entries_1063_ = lean_ctor_get(v_map_1061_, 0);
lean_inc_ref(v_entries_1063_);
lean_dec_ref(v_map_1061_);
v___x_1064_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = lean_array_get_size(v_entries_1063_);
v___x_1067_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1068_ = lean_nat_dec_lt(v___x_1065_, v___x_1066_);
if (v___x_1068_ == 0)
{
lean_dec_ref(v_entries_1063_);
lean_dec_ref(v_keys_1062_);
lean_dec_ref(v_inst_1060_);
lean_dec_ref(v_inst_1059_);
return v___x_1064_;
}
else
{
lean_object* v___f_1069_; uint8_t v___x_1070_; 
v___f_1069_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1069_, 0, v_inst_1059_);
lean_closure_set(v___f_1069_, 1, v_keys_1062_);
lean_closure_set(v___f_1069_, 2, v_inst_1060_);
v___x_1070_ = lean_nat_dec_le(v___x_1066_, v___x_1066_);
if (v___x_1070_ == 0)
{
if (v___x_1068_ == 0)
{
lean_dec_ref(v___f_1069_);
lean_dec_ref(v_entries_1063_);
return v___x_1064_;
}
else
{
size_t v___x_1071_; size_t v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = ((size_t)0ULL);
v___x_1072_ = lean_usize_of_nat(v___x_1066_);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1067_, v___f_1069_, v_entries_1063_, v___x_1071_, v___x_1072_, v___x_1064_);
return v___x_1073_;
}
}
else
{
size_t v___x_1074_; size_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = ((size_t)0ULL);
v___x_1075_ = lean_usize_of_nat(v___x_1066_);
v___x_1076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1067_, v___f_1069_, v_entries_1063_, v___x_1074_, v___x_1075_, v___x_1064_);
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany(lean_object* v_00_u03b1_1077_, lean_object* v_00_u03b2_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_map_1083_, lean_object* v_keys_1084_){
_start:
{
lean_object* v_entries_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v_entries_1085_ = lean_ctor_get(v_map_1083_, 0);
lean_inc_ref(v_entries_1085_);
lean_dec_ref(v_map_1083_);
v___x_1086_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_array_get_size(v_entries_1085_);
v___x_1089_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1090_ = lean_nat_dec_lt(v___x_1087_, v___x_1088_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v_entries_1085_);
lean_dec_ref(v_keys_1084_);
lean_dec_ref(v_inst_1080_);
lean_dec_ref(v_inst_1079_);
return v___x_1086_;
}
else
{
lean_object* v___f_1091_; uint8_t v___x_1092_; 
v___f_1091_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1091_, 0, v_inst_1079_);
lean_closure_set(v___f_1091_, 1, v_keys_1084_);
lean_closure_set(v___f_1091_, 2, v_inst_1080_);
v___x_1092_ = lean_nat_dec_le(v___x_1088_, v___x_1088_);
if (v___x_1092_ == 0)
{
if (v___x_1090_ == 0)
{
lean_dec_ref(v___f_1091_);
lean_dec_ref(v_entries_1085_);
return v___x_1086_;
}
else
{
size_t v___x_1093_; size_t v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = ((size_t)0ULL);
v___x_1094_ = lean_usize_of_nat(v___x_1088_);
v___x_1095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1089_, v___f_1091_, v_entries_1085_, v___x_1093_, v___x_1094_, v___x_1086_);
return v___x_1095_;
}
}
else
{
size_t v___x_1096_; size_t v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = ((size_t)0ULL);
v___x_1097_ = lean_usize_of_nat(v___x_1088_);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1089_, v___f_1091_, v_entries_1085_, v___x_1096_, v___x_1097_, v___x_1086_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg(lean_object* v_map_1099_){
_start:
{
lean_object* v_entries_1100_; lean_object* v___x_1101_; 
v_entries_1100_ = lean_ctor_get(v_map_1099_, 0);
v___x_1101_ = lean_array_get_size(v_entries_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg___boxed(lean_object* v_map_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_Internal_IndexMultiMap_size___redArg(v_map_1102_);
lean_dec_ref(v_map_1102_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_map_1108_){
_start:
{
lean_object* v_entries_1109_; lean_object* v___x_1110_; 
v_entries_1109_ = lean_ctor_get(v_map_1108_, 0);
v___x_1110_ = lean_array_get_size(v_entries_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___boxed(lean_object* v_00_u03b1_1111_, lean_object* v_00_u03b2_1112_, lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_map_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Std_Internal_IndexMultiMap_size(v_00_u03b1_1111_, v_00_u03b2_1112_, v_inst_1113_, v_inst_1114_, v_map_1115_);
lean_dec_ref(v_map_1115_);
lean_dec_ref(v_inst_1114_);
lean_dec_ref(v_inst_1113_);
return v_res_1116_;
}
}
uint8_t l_Std_Internal_IndexMultiMap_isEmpty___redArg(lean_object* v_map_1117_){
_start:
{
lean_object* v_entries_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_entries_1118_ = lean_ctor_get(v_map_1117_, 0);
v___x_1119_ = lean_array_get_size(v_entries_1118_);
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_nat_dec_eq(v___x_1119_, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_1117_ = stack[0].m_obj;
uint8_t v_res_1122_;
v_res_1122_ = l_Std_Internal_IndexMultiMap_isEmpty___redArg(v_map_1117_);
stack->m_num = v_res_1122_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___redArg___boxed(lean_object* v_map_1123_){
_start:
{
uint8_t v_res_1124_; lean_object* v_r_1125_; 
v_res_1124_ = l_Std_Internal_IndexMultiMap_isEmpty___redArg(v_map_1123_);
lean_dec_ref(v_map_1123_);
v_r_1125_ = lean_box(v_res_1124_);
return v_r_1125_;
}
}
uint8_t l_Std_Internal_IndexMultiMap_isEmpty(lean_object* v_00_u03b1_1126_, lean_object* v_00_u03b2_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_map_1130_){
_start:
{
lean_object* v_entries_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_entries_1131_ = lean_ctor_get(v_map_1130_, 0);
v___x_1132_ = lean_array_get_size(v_entries_1131_);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_nat_dec_eq(v___x_1132_, v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1128_ = stack[2].m_obj;
lean_object* v_inst_1129_ = stack[3].m_obj;
lean_object* v_map_1130_ = stack[4].m_obj;
uint8_t v_res_1135_;
v_res_1135_ = l_Std_Internal_IndexMultiMap_isEmpty(lean_box(0), lean_box(0), v_inst_1128_, v_inst_1129_, v_map_1130_);
stack->m_num = v_res_1135_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_00_u03b2_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_map_1140_){
_start:
{
uint8_t v_res_1141_; lean_object* v_r_1142_; 
v_res_1141_ = l_Std_Internal_IndexMultiMap_isEmpty(v_00_u03b1_1136_, v_00_u03b2_1137_, v_inst_1138_, v_inst_1139_, v_map_1140_);
lean_dec_ref(v_map_1140_);
lean_dec_ref(v_inst_1139_);
lean_dec_ref(v_inst_1138_);
v_r_1142_ = lean_box(v_res_1141_);
return v_r_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg(lean_object* v_map_1143_){
_start:
{
lean_object* v_entries_1144_; 
v_entries_1144_ = lean_ctor_get(v_map_1143_, 0);
lean_inc_ref(v_entries_1144_);
return v_entries_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg___boxed(lean_object* v_map_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Std_Internal_IndexMultiMap_toArray___redArg(v_map_1145_);
lean_dec_ref(v_map_1145_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray(lean_object* v_00_u03b1_1147_, lean_object* v_00_u03b2_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_map_1151_){
_start:
{
lean_object* v_entries_1152_; 
v_entries_1152_ = lean_ctor_get(v_map_1151_, 0);
lean_inc_ref(v_entries_1152_);
return v_entries_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___boxed(lean_object* v_00_u03b1_1153_, lean_object* v_00_u03b2_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_map_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Std_Internal_IndexMultiMap_toArray(v_00_u03b1_1153_, v_00_u03b2_1154_, v_inst_1155_, v_inst_1156_, v_map_1157_);
lean_dec_ref(v_map_1157_);
lean_dec_ref(v_inst_1156_);
lean_dec_ref(v_inst_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___redArg(lean_object* v_map_1159_){
_start:
{
lean_object* v_entries_1160_; lean_object* v___x_1161_; 
v_entries_1160_ = lean_ctor_get(v_map_1159_, 0);
lean_inc_ref(v_entries_1160_);
lean_dec_ref(v_map_1159_);
v___x_1161_ = lean_array_to_list(v_entries_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList(lean_object* v_00_u03b1_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_map_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Std_Internal_IndexMultiMap_toList___redArg(v_map_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___boxed(lean_object* v_00_u03b1_1168_, lean_object* v_00_u03b2_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_map_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Std_Internal_IndexMultiMap_toList(v_00_u03b1_1168_, v_00_u03b2_1169_, v_inst_1170_, v_inst_1171_, v_map_1172_);
lean_dec_ref(v_inst_1171_);
lean_dec_ref(v_inst_1170_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg___lam__1(lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_x1_1176_, lean_object* v_x2_1177_){
_start:
{
lean_object* v_fst_1178_; lean_object* v_entries_1179_; lean_object* v_indexes_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1191_; 
v_fst_1178_ = lean_ctor_get(v_x2_1177_, 0);
lean_inc(v_fst_1178_);
v_entries_1179_ = lean_ctor_get(v_x1_1176_, 0);
v_indexes_1180_ = lean_ctor_get(v_x1_1176_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_x1_1176_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1182_ = v_x1_1176_;
v_isShared_1183_ = v_isSharedCheck_1191_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_indexes_1180_);
lean_inc(v_entries_1179_);
lean_dec(v_x1_1176_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1191_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_i_1184_; lean_object* v_f_1185_; lean_object* v_entries_1186_; lean_object* v_indexes_1187_; lean_object* v___x_1189_; 
v_i_1184_ = lean_array_get_size(v_entries_1179_);
v_f_1185_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1185_, 0, v_i_1184_);
v_entries_1186_ = lean_array_push(v_entries_1179_, v_x2_1177_);
v_indexes_1187_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1174_, v_inst_1175_, v_indexes_1180_, v_fst_1178_, v_f_1185_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v_indexes_1187_);
lean_ctor_set(v___x_1182_, 0, v_entries_1186_);
v___x_1189_ = v___x_1182_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_entries_1186_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_indexes_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg(lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_m1_1194_, lean_object* v_m2_1195_){
_start:
{
lean_object* v_entries_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_entries_1196_ = lean_ctor_get(v_m2_1195_, 0);
lean_inc_ref(v_entries_1196_);
lean_dec_ref(v_m2_1195_);
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_array_get_size(v_entries_1196_);
v___x_1199_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1200_ = lean_nat_dec_lt(v___x_1197_, v___x_1198_);
if (v___x_1200_ == 0)
{
lean_dec_ref(v_entries_1196_);
lean_dec_ref(v_inst_1193_);
lean_dec_ref(v_inst_1192_);
return v_m1_1194_;
}
else
{
lean_object* v___f_1201_; uint8_t v___x_1202_; 
v___f_1201_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1201_, 0, v_inst_1192_);
lean_closure_set(v___f_1201_, 1, v_inst_1193_);
v___x_1202_ = lean_nat_dec_le(v___x_1198_, v___x_1198_);
if (v___x_1202_ == 0)
{
if (v___x_1200_ == 0)
{
lean_dec_ref(v___f_1201_);
lean_dec_ref(v_entries_1196_);
return v_m1_1194_;
}
else
{
size_t v___x_1203_; size_t v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = ((size_t)0ULL);
v___x_1204_ = lean_usize_of_nat(v___x_1198_);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1199_, v___f_1201_, v_entries_1196_, v___x_1203_, v___x_1204_, v_m1_1194_);
return v___x_1205_;
}
}
else
{
size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = lean_usize_of_nat(v___x_1198_);
v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1199_, v___f_1201_, v_entries_1196_, v___x_1206_, v___x_1207_, v_m1_1194_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge(lean_object* v_00_u03b1_1209_, lean_object* v_00_u03b2_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_m1_1215_, lean_object* v_m2_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Std_Internal_IndexMultiMap_merge___redArg(v_inst_1211_, v_inst_1212_, v_m1_1215_, v_m2_1216_);
return v___x_1217_;
}
}
lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
return v___x_1219_;
}
}
LEAN_EXPORT void l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1220_;
v_res_1220_ = l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg();
stack->m_obj
 = v_res_1220_;
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg();
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection(lean_object* v_00_u03b1_1223_, lean_object* v_00_u03b2_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_00_u03b2_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Std_Internal_IndexMultiMap_instEmptyCollection(v_00_u03b1_1228_, v_00_u03b2_1229_, v_inst_1230_, v_inst_1231_);
lean_dec_ref(v_inst_1231_);
lean_dec_ref(v_inst_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_x_1235_){
_start:
{
lean_object* v_fst_1236_; lean_object* v___x_1237_; lean_object* v_entries_1238_; lean_object* v_indexes_1239_; lean_object* v_i_1240_; lean_object* v_f_1241_; lean_object* v_entries_1242_; lean_object* v_indexes_1243_; lean_object* v___x_1244_; 
v_fst_1236_ = lean_ctor_get(v_x_1235_, 0);
lean_inc(v_fst_1236_);
v___x_1237_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v_entries_1238_ = lean_ctor_get(v___x_1237_, 0);
v_indexes_1239_ = lean_ctor_get(v___x_1237_, 1);
v_i_1240_ = lean_array_get_size(v_entries_1238_);
v_f_1241_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1241_, 0, v_i_1240_);
lean_inc_ref(v_entries_1238_);
v_entries_1242_ = lean_array_push(v_entries_1238_, v_x_1235_);
lean_inc_ref(v_indexes_1239_);
v_indexes_1243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1233_, v_inst_1234_, v_indexes_1239_, v_fst_1236_, v_f_1241_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_entries_1242_);
lean_ctor_set(v___x_1244_, 1, v_indexes_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1245_, lean_object* v_inst_1246_){
_start:
{
lean_object* v___f_1247_; 
v___f_1247_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1247_, 0, v_inst_1245_);
lean_closure_set(v___f_1247_, 1, v_inst_1246_);
return v___f_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1248_, lean_object* v_00_u03b2_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_){
_start:
{
lean_object* v___f_1254_; 
v___f_1254_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1254_, 0, v_inst_1250_);
lean_closure_set(v___f_1254_, 1, v_inst_1251_);
return v___f_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_x_1257_, lean_object* v_m_1258_){
_start:
{
lean_object* v_fst_1259_; lean_object* v_entries_1260_; lean_object* v_indexes_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1272_; 
v_fst_1259_ = lean_ctor_get(v_x_1257_, 0);
lean_inc(v_fst_1259_);
v_entries_1260_ = lean_ctor_get(v_m_1258_, 0);
v_indexes_1261_ = lean_ctor_get(v_m_1258_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_m_1258_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1263_ = v_m_1258_;
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_indexes_1261_);
lean_inc(v_entries_1260_);
lean_dec(v_m_1258_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v_i_1265_; lean_object* v_f_1266_; lean_object* v_entries_1267_; lean_object* v_indexes_1268_; lean_object* v___x_1270_; 
v_i_1265_ = lean_array_get_size(v_entries_1260_);
v_f_1266_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1266_, 0, v_i_1265_);
v_entries_1267_ = lean_array_push(v_entries_1260_, v_x_1257_);
v_indexes_1268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1255_, v_inst_1256_, v_indexes_1261_, v_fst_1259_, v_f_1266_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v_indexes_1268_);
lean_ctor_set(v___x_1263_, 0, v_entries_1267_);
v___x_1270_ = v___x_1263_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_entries_1267_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_indexes_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1273_, lean_object* v_inst_1274_){
_start:
{
lean_object* v___f_1275_; 
v___f_1275_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1275_, 0, v_inst_1273_);
lean_closure_set(v___f_1275_, 1, v_inst_1274_);
return v___f_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1276_, lean_object* v_00_u03b2_1277_, lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_){
_start:
{
lean_object* v___f_1282_; 
v___f_1282_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1282_, 0, v_inst_1278_);
lean_closure_set(v___f_1282_, 1, v_inst_1279_);
return v___f_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1283_, lean_object* v_inst_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1285_, 0, lean_box(0));
lean_closure_set(v___x_1285_, 1, lean_box(0));
lean_closure_set(v___x_1285_, 2, v_inst_1283_);
lean_closure_set(v___x_1285_, 3, v_inst_1284_);
lean_closure_set(v___x_1285_, 4, lean_box(0));
lean_closure_set(v___x_1285_, 5, lean_box(0));
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1286_, lean_object* v_00_u03b2_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1292_, 0, lean_box(0));
lean_closure_set(v___x_1292_, 1, lean_box(0));
lean_closure_set(v___x_1292_, 2, v_inst_1288_);
lean_closure_set(v___x_1292_, 3, v_inst_1289_);
lean_closure_set(v___x_1292_, 4, lean_box(0));
lean_closure_set(v___x_1292_, 5, lean_box(0));
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1293_, lean_object* v_a_1294_, lean_object* v_x_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_apply_2(v_f_1293_, v_a_1294_, v___y_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1298_, lean_object* v_00_u03b2_1299_, lean_object* v_map_1300_, lean_object* v_b_1301_, lean_object* v_f_1302_){
_start:
{
lean_object* v_entries_1303_; lean_object* v___f_1304_; size_t v_sz_1305_; size_t v___x_1306_; lean_object* v___x_1307_; 
v_entries_1303_ = lean_ctor_get(v_map_1300_, 0);
lean_inc_ref(v_entries_1303_);
lean_dec_ref(v_map_1300_);
v___f_1304_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1304_, 0, v_f_1302_);
v_sz_1305_ = lean_array_size(v_entries_1303_);
v___x_1306_ = ((size_t)0ULL);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1298_, v_entries_1303_, v___f_1304_, v_sz_1305_, v___x_1306_, v_b_1301_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg(lean_object* v_inst_1308_){
_start:
{
lean_object* v___f_1309_; 
v___f_1309_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1309_, 0, v_inst_1308_);
return v___f_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad(lean_object* v_00_u03b1_1310_, lean_object* v_00_u03b2_1311_, lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_m_1314_, lean_object* v_inst_1315_){
_start:
{
lean_object* v___f_1316_; 
v___f_1316_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1316_, 0, v_inst_1315_);
return v___f_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_00_u03b2_1318_, lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_m_1321_, lean_object* v_inst_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Std_Internal_IndexMultiMap_instForInProdOfMonad(v_00_u03b1_1317_, v_00_u03b2_1318_, v_inst_1319_, v_inst_1320_, v_m_1321_, v_inst_1322_);
lean_dec_ref(v_inst_1320_);
lean_dec_ref(v_inst_1319_);
return v_res_1323_;
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
