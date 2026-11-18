// Lean compiler output
// Module: Std.Http.Internal.MultiMap
// Imports: public import Init.Data.Array.Lemmas public import Init.Data.Option.BasicAux import Init.Omega
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_mk(lean_object*);
static const lean_array_object l_Std_Internal_instInhabitedMultiMap_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_instInhabitedMultiMap_default___redArg___closed__0 = (const lean_object*)&l_Std_Internal_instInhabitedMultiMap_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedMultiMap_default___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedMultiMap_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Internal_instInhabitedMultiMap_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedMultiMap_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedMultiMap_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedMultiMap___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedMultiMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedMultiMap(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_instReprMultiMap_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__0 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Internal_instReprMultiMap_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entries"};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__1 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Internal_instReprMultiMap_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__2 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Internal_instReprMultiMap_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__3 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Internal_instReprMultiMap_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__4 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Internal_instReprMultiMap_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__5 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Internal_instReprMultiMap_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__3_value),((lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__6 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Internal_instReprMultiMap_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__7;
static const lean_string_object l_Std_Internal_instReprMultiMap_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__8 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__8_value;
static lean_once_cell_t l_Std_Internal_instReprMultiMap_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__9;
static lean_once_cell_t l_Std_Internal_instReprMultiMap_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__10;
static const lean_ctor_object l_Std_Internal_instReprMultiMap_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__11 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__11_value;
static const lean_ctor_object l_Std_Internal_instReprMultiMap_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Internal_instReprMultiMap_repr___redArg___closed__12 = (const lean_object*)&l_Std_Internal_instReprMultiMap_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instMembershipOfBEq___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instMembershipOfBEq___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instMembershipOfBEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instMembershipOfBEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_instDecidableMem___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__0 = (const lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__0_value;
static const lean_closure_object l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__1 = (const lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__1_value;
static const lean_closure_object l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__2 = (const lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__2_value;
static const lean_closure_object l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__3 = (const lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__3_value;
static const lean_closure_object l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__4 = (const lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__4_value;
static const lean_closure_object l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__5 = (const lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__5_value;
static const lean_closure_object l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__6 = (const lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__6_value;
static const lean_ctor_object l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__0_value),((lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__1_value)}};
static const lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__7 = (const lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__7_value;
static const lean_ctor_object l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__7_value),((lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__2_value),((lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__3_value),((lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__4_value),((lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__5_value)}};
static const lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__8 = (const lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__8_value;
static const lean_ctor_object l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__8_value),((lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__6_value)}};
static const lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9 = (const lean_object*)&l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9_value;
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Internal_MultiMap_getAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_MultiMap_getAll___redArg___closed__0 = (const lean_object*)&l_Std_Internal_MultiMap_getAll___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getAll_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getAll_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_hasEntry___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_hasEntry___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_hasEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_hasEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_hasEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_hasEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getLast_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getLast_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getLast_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getLast_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_MultiMap_get_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_Internal_MultiMap_get_x21___redArg___closed__0 = (const lean_object*)&l_Std_Internal_MultiMap_get_x21___redArg___closed__0_value;
static const lean_string_object l_Std_Internal_MultiMap_get_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_Internal_MultiMap_get_x21___redArg___closed__1 = (const lean_object*)&l_Std_Internal_MultiMap_get_x21___redArg___closed__1_value;
static const lean_string_object l_Std_Internal_MultiMap_get_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_Internal_MultiMap_get_x21___redArg___closed__2 = (const lean_object*)&l_Std_Internal_MultiMap_get_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_Internal_MultiMap_get_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_MultiMap_get_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_insertMany___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Internal_MultiMap_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_MultiMap_empty___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_ofList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_ofList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_update___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_update___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_update(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_replaceLast___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_replaceLast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_erase___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Internal_MultiMap_erase___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_MultiMap_erase___redArg___closed__0 = (const lean_object*)&l_Std_Internal_MultiMap_erase___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_eraseMany___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_eraseMany___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_eraseMany___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_eraseMany___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_eraseMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_toArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_toArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_merge___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_merge___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_merge(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_merge___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instSingletonProd___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_Internal_MultiMap_instSingletonProd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_MultiMap_instSingletonProd___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_MultiMap_instSingletonProd___redArg___closed__0 = (const lean_object*)&l_Std_Internal_MultiMap_instSingletonProd___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instSingletonProd___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instSingletonProd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instSingletonProd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instInsertProd___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_MultiMap_instInsertProd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_MultiMap_instInsertProd___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_MultiMap_instInsertProd___redArg___closed__0 = (const lean_object*)&l_Std_Internal_MultiMap_instInsertProd___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instInsertProd___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instInsertProd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instInsertProd(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_MultiMap_instUnion___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_MultiMap_merge___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Internal_MultiMap_instUnion___redArg___closed__0 = (const lean_object*)&l_Std_Internal_MultiMap_instUnion___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instUnion___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instUnion___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instUnion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instForInProdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instForInProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instForInProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedMultiMap_default___redArg(){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_Std_Internal_instInhabitedMultiMap_default___redArg___closed__0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedMultiMap_default___redArg___boxed(lean_object* v___dummy_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Std_Internal_instInhabitedMultiMap_default___redArg();
return v_res_6_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedMultiMap_default___closed__0(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Std_Internal_instInhabitedMultiMap_default___redArg();
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedMultiMap_default(lean_object* v_00_u03b1_8_, lean_object* v_00_u03b2_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Std_Internal_instInhabitedMultiMap_default___closed__0, &l_Std_Internal_instInhabitedMultiMap_default___closed__0_once, _init_l_Std_Internal_instInhabitedMultiMap_default___closed__0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedMultiMap___redArg(){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Std_Internal_instInhabitedMultiMap_default___closed__0, &l_Std_Internal_instInhabitedMultiMap_default___closed__0_once, _init_l_Std_Internal_instInhabitedMultiMap_default___closed__0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedMultiMap___redArg___boxed(lean_object* v___dummy_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Internal_instInhabitedMultiMap___redArg();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedMultiMap(lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_once(&l_Std_Internal_instInhabitedMultiMap_default___closed__0, &l_Std_Internal_instInhabitedMultiMap_default___closed__0_once, _init_l_Std_Internal_instInhabitedMultiMap_default___closed__0);
return v___x_17_;
}
}
static lean_object* _init_l_Std_Internal_instReprMultiMap_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_unsigned_to_nat(11u);
v___x_32_ = lean_nat_to_int(v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_l_Std_Internal_instReprMultiMap_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = ((lean_object*)(l_Std_Internal_instReprMultiMap_repr___redArg___closed__0));
v___x_35_ = lean_string_length(v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Std_Internal_instReprMultiMap_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_obj_once(&l_Std_Internal_instReprMultiMap_repr___redArg___closed__9, &l_Std_Internal_instReprMultiMap_repr___redArg___closed__9_once, _init_l_Std_Internal_instReprMultiMap_repr___redArg___closed__9);
v___x_37_ = lean_nat_to_int(v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap_repr___redArg(lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_x_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_45_ = ((lean_object*)(l_Std_Internal_instReprMultiMap_repr___redArg___closed__6));
v___x_46_ = lean_obj_once(&l_Std_Internal_instReprMultiMap_repr___redArg___closed__7, &l_Std_Internal_instReprMultiMap_repr___redArg___closed__7_once, _init_l_Std_Internal_instReprMultiMap_repr___redArg___closed__7);
v___f_47_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_47_, 0, v_inst_43_);
v___x_48_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_48_, 0, lean_box(0));
lean_closure_set(v___x_48_, 1, lean_box(0));
lean_closure_set(v___x_48_, 2, v_inst_42_);
lean_closure_set(v___x_48_, 3, v___f_47_);
v___x_49_ = l_Array_repr___redArg(v___x_48_, v_x_44_);
v___x_50_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_46_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
v___x_51_ = 0;
v___x_52_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_52_, 0, v___x_50_);
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*1, v___x_51_);
v___x_53_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_45_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = lean_obj_once(&l_Std_Internal_instReprMultiMap_repr___redArg___closed__10, &l_Std_Internal_instReprMultiMap_repr___redArg___closed__10_once, _init_l_Std_Internal_instReprMultiMap_repr___redArg___closed__10);
v___x_55_ = ((lean_object*)(l_Std_Internal_instReprMultiMap_repr___redArg___closed__11));
v___x_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_53_);
v___x_57_ = ((lean_object*)(l_Std_Internal_instReprMultiMap_repr___redArg___closed__12));
v___x_58_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_54_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set_uint8(v___x_60_, sizeof(void*)*1, v___x_51_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap_repr(lean_object* v_00_u03b1_61_, lean_object* v_00_u03b2_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_x_65_, lean_object* v_prec_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Std_Internal_instReprMultiMap_repr___redArg(v_inst_63_, v_inst_64_, v_x_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap_repr___boxed(lean_object* v_00_u03b1_68_, lean_object* v_00_u03b2_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_x_72_, lean_object* v_prec_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Std_Internal_instReprMultiMap_repr(v_00_u03b1_68_, v_00_u03b2_69_, v_inst_70_, v_inst_71_, v_x_72_, v_prec_73_);
lean_dec(v_prec_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap___redArg(lean_object* v_inst_75_, lean_object* v_inst_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_closure((void*)(l_Std_Internal_instReprMultiMap_repr___boxed), 6, 4);
lean_closure_set(v___x_77_, 0, lean_box(0));
lean_closure_set(v___x_77_, 1, lean_box(0));
lean_closure_set(v___x_77_, 2, v_inst_75_);
lean_closure_set(v___x_77_, 3, v_inst_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprMultiMap(lean_object* v_00_u03b1_78_, lean_object* v_00_u03b2_79_, lean_object* v_inst_80_, lean_object* v_inst_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_alloc_closure((void*)(l_Std_Internal_instReprMultiMap_repr___boxed), 6, 4);
lean_closure_set(v___x_82_, 0, lean_box(0));
lean_closure_set(v___x_82_, 1, lean_box(0));
lean_closure_set(v___x_82_, 2, v_inst_80_);
lean_closure_set(v___x_82_, 3, v_inst_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instMembershipOfBEq___redArg(){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instMembershipOfBEq___redArg___boxed(lean_object* v___dummy_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Internal_MultiMap_instMembershipOfBEq___redArg();
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instMembershipOfBEq(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_inst_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(0);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instMembershipOfBEq___boxed(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_inst_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_Internal_MultiMap_instMembershipOfBEq(v_00_u03b1_91_, v_00_u03b2_92_, v_inst_93_);
lean_dec_ref(v_inst_93_);
return v_res_94_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_instDecidableMem___redArg___lam__0(lean_object* v_inst_95_, lean_object* v_key_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_fst_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_fst_98_ = lean_ctor_get(v_x_97_, 0);
lean_inc(v_fst_98_);
lean_dec_ref(v_x_97_);
v___x_99_ = lean_apply_2(v_inst_95_, v_fst_98_, v_key_96_);
v___x_100_ = lean_unbox(v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___lam__0___boxed(lean_object* v_inst_101_, lean_object* v_key_102_, lean_object* v_x_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Std_Internal_MultiMap_instDecidableMem___redArg___lam__0(v_inst_101_, v_key_102_, v_x_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_instDecidableMem___redArg(lean_object* v_inst_125_, lean_object* v_key_126_, lean_object* v_map_127_){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_array_get_size(v_map_127_);
v___x_130_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_131_ = lean_nat_dec_lt(v___x_128_, v___x_129_);
if (v___x_131_ == 0)
{
lean_dec_ref(v_map_127_);
lean_dec(v_key_126_);
lean_dec_ref(v_inst_125_);
return v___x_131_;
}
else
{
if (v___x_131_ == 0)
{
lean_dec_ref(v_map_127_);
lean_dec(v_key_126_);
lean_dec_ref(v_inst_125_);
return v___x_131_;
}
else
{
lean_object* v___f_132_; size_t v___x_133_; size_t v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___f_132_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_132_, 0, v_inst_125_);
lean_closure_set(v___f_132_, 1, v_key_126_);
v___x_133_ = ((size_t)0ULL);
v___x_134_ = lean_usize_of_nat(v___x_129_);
v___x_135_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_130_, v___f_132_, v_map_127_, v___x_133_, v___x_134_);
v___x_136_ = lean_unbox(v___x_135_);
lean_dec(v___x_135_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instDecidableMem___redArg___boxed(lean_object* v_inst_137_, lean_object* v_key_138_, lean_object* v_map_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Std_Internal_MultiMap_instDecidableMem___redArg(v_inst_137_, v_key_138_, v_map_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_instDecidableMem(lean_object* v_00_u03b1_142_, lean_object* v_00_u03b2_143_, lean_object* v_inst_144_, lean_object* v_key_145_, lean_object* v_map_146_){
_start:
{
uint8_t v___x_147_; 
v___x_147_ = l_Std_Internal_MultiMap_instDecidableMem___redArg(v_inst_144_, v_key_145_, v_map_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instDecidableMem___boxed(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_inst_150_, lean_object* v_key_151_, lean_object* v_map_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Std_Internal_MultiMap_instDecidableMem(v_00_u03b1_148_, v_00_u03b2_149_, v_inst_150_, v_key_151_, v_map_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___redArg(lean_object* v_inst_155_, lean_object* v_map_156_, lean_object* v_key_157_, lean_object* v_i_158_){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_array_get_size(v_map_156_);
v___x_160_ = lean_nat_dec_lt(v_i_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_dec(v_i_158_);
lean_dec(v_key_157_);
lean_dec_ref(v_inst_155_);
return v___x_159_;
}
else
{
lean_object* v___x_161_; lean_object* v_fst_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_161_ = lean_array_fget_borrowed(v_map_156_, v_i_158_);
v_fst_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc_ref(v_inst_155_);
lean_inc(v_key_157_);
lean_inc(v_fst_162_);
v___x_163_ = lean_apply_2(v_inst_155_, v_fst_162_, v_key_157_);
v___x_164_ = lean_unbox(v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_add(v_i_158_, v___x_165_);
lean_dec(v_i_158_);
v_i_158_ = v___x_166_;
goto _start;
}
else
{
lean_dec(v_key_157_);
lean_dec_ref(v_inst_155_);
return v_i_158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___redArg___boxed(lean_object* v_inst_168_, lean_object* v_map_169_, lean_object* v_key_170_, lean_object* v_i_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v_inst_168_, v_map_169_, v_key_170_, v_i_171_);
lean_dec_ref(v_map_169_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom(lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_inst_175_, lean_object* v_map_176_, lean_object* v_key_177_, lean_object* v_i_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v_inst_175_, v_map_176_, v_key_177_, v_i_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___boxed(lean_object* v_00_u03b1_180_, lean_object* v_00_u03b2_181_, lean_object* v_inst_182_, lean_object* v_map_183_, lean_object* v_key_184_, lean_object* v_i_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_Internal_MultiMap_findIdxFrom(v_00_u03b1_180_, v_00_u03b2_181_, v_inst_182_, v_map_183_, v_key_184_, v_i_185_);
lean_dec_ref(v_map_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___redArg(lean_object* v_inst_187_, lean_object* v_map_188_, lean_object* v_key_189_, lean_object* v_x_190_){
_start:
{
lean_object* v_zero_191_; uint8_t v_isZero_192_; 
v_zero_191_ = lean_unsigned_to_nat(0u);
v_isZero_192_ = lean_nat_dec_eq(v_x_190_, v_zero_191_);
if (v_isZero_192_ == 1)
{
lean_object* v___x_193_; 
lean_dec(v_x_190_);
lean_dec(v_key_189_);
lean_dec_ref(v_inst_187_);
v___x_193_ = lean_array_get_size(v_map_188_);
return v___x_193_;
}
else
{
lean_object* v_one_194_; lean_object* v_n_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_one_194_ = lean_unsigned_to_nat(1u);
v_n_195_ = lean_nat_sub(v_x_190_, v_one_194_);
lean_dec(v_x_190_);
v___x_196_ = lean_array_get_size(v_map_188_);
v___x_197_ = lean_nat_dec_lt(v_n_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_dec(v_n_195_);
lean_dec(v_key_189_);
lean_dec_ref(v_inst_187_);
return v___x_196_;
}
else
{
lean_object* v___x_198_; lean_object* v_fst_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_198_ = lean_array_fget_borrowed(v_map_188_, v_n_195_);
v_fst_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc_ref(v_inst_187_);
lean_inc(v_key_189_);
lean_inc(v_fst_199_);
v___x_200_ = lean_apply_2(v_inst_187_, v_fst_199_, v_key_189_);
v___x_201_ = lean_unbox(v___x_200_);
if (v___x_201_ == 0)
{
v_x_190_ = v_n_195_;
goto _start;
}
else
{
lean_dec(v_key_189_);
lean_dec_ref(v_inst_187_);
return v_n_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___redArg___boxed(lean_object* v_inst_203_, lean_object* v_map_204_, lean_object* v_key_205_, lean_object* v_x_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Internal_MultiMap_findLastIdxBelow___redArg(v_inst_203_, v_map_204_, v_key_205_, v_x_206_);
lean_dec_ref(v_map_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_, lean_object* v_inst_210_, lean_object* v_map_211_, lean_object* v_key_212_, lean_object* v_x_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_Internal_MultiMap_findLastIdxBelow___redArg(v_inst_210_, v_map_211_, v_key_212_, v_x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___boxed(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_, lean_object* v_inst_217_, lean_object* v_map_218_, lean_object* v_key_219_, lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_Internal_MultiMap_findLastIdxBelow(v_00_u03b1_215_, v_00_u03b2_216_, v_inst_217_, v_map_218_, v_key_219_, v_x_220_);
lean_dec_ref(v_map_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getAll___redArg___lam__0(lean_object* v_inst_222_, lean_object* v_key_223_, lean_object* v_x1_224_, lean_object* v_x2_225_){
_start:
{
lean_object* v_fst_226_; lean_object* v_snd_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_fst_226_ = lean_ctor_get(v_x2_225_, 0);
lean_inc(v_fst_226_);
v_snd_227_ = lean_ctor_get(v_x2_225_, 1);
lean_inc(v_snd_227_);
lean_dec_ref(v_x2_225_);
v___x_228_ = lean_apply_2(v_inst_222_, v_fst_226_, v_key_223_);
v___x_229_ = lean_unbox(v___x_228_);
if (v___x_229_ == 0)
{
lean_dec(v_snd_227_);
return v_x1_224_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = lean_array_push(v_x1_224_, v_snd_227_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getAll___redArg(lean_object* v_inst_233_, lean_object* v_map_234_, lean_object* v_key_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = ((lean_object*)(l_Std_Internal_MultiMap_getAll___redArg___closed__0));
v___x_238_ = lean_array_get_size(v_map_234_);
v___x_239_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_240_ = lean_nat_dec_lt(v___x_236_, v___x_238_);
if (v___x_240_ == 0)
{
lean_dec(v_key_235_);
lean_dec_ref(v_map_234_);
lean_dec_ref(v_inst_233_);
return v___x_237_;
}
else
{
lean_object* v___f_241_; size_t v___x_242_; size_t v___x_243_; lean_object* v___x_244_; 
v___f_241_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_getAll___redArg___lam__0), 4, 2);
lean_closure_set(v___f_241_, 0, v_inst_233_);
lean_closure_set(v___f_241_, 1, v_key_235_);
v___x_242_ = ((size_t)0ULL);
v___x_243_ = lean_usize_of_nat(v___x_238_);
v___x_244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_239_, v___f_241_, v_map_234_, v___x_242_, v___x_243_, v___x_237_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getAll(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_inst_247_, lean_object* v_map_248_, lean_object* v_key_249_, lean_object* v___h_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = ((lean_object*)(l_Std_Internal_MultiMap_getAll___redArg___closed__0));
v___x_253_ = lean_array_get_size(v_map_248_);
v___x_254_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_255_ = lean_nat_dec_lt(v___x_251_, v___x_253_);
if (v___x_255_ == 0)
{
lean_dec(v_key_249_);
lean_dec_ref(v_map_248_);
lean_dec_ref(v_inst_247_);
return v___x_252_;
}
else
{
lean_object* v___f_256_; size_t v___x_257_; size_t v___x_258_; lean_object* v___x_259_; 
v___f_256_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_getAll___redArg___lam__0), 4, 2);
lean_closure_set(v___f_256_, 0, v_inst_247_);
lean_closure_set(v___f_256_, 1, v_key_249_);
v___x_257_ = ((size_t)0ULL);
v___x_258_ = lean_usize_of_nat(v___x_253_);
v___x_259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_254_, v___f_256_, v_map_248_, v___x_257_, v___x_258_, v___x_252_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get___redArg(lean_object* v_inst_260_, lean_object* v_map_261_, lean_object* v_key_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_snd_266_; 
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v_inst_260_, v_map_261_, v_key_262_, v___x_263_);
v___x_265_ = lean_array_fget_borrowed(v_map_261_, v___x_264_);
lean_dec(v___x_264_);
v_snd_266_ = lean_ctor_get(v___x_265_, 1);
lean_inc(v_snd_266_);
return v_snd_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get___redArg___boxed(lean_object* v_inst_267_, lean_object* v_map_268_, lean_object* v_key_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_Internal_MultiMap_get___redArg(v_inst_267_, v_map_268_, v_key_269_);
lean_dec_ref(v_map_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get(lean_object* v_00_u03b1_271_, lean_object* v_00_u03b2_272_, lean_object* v_inst_273_, lean_object* v_map_274_, lean_object* v_key_275_, lean_object* v_h_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_snd_280_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v_inst_273_, v_map_274_, v_key_275_, v___x_277_);
v___x_279_ = lean_array_fget_borrowed(v_map_274_, v___x_278_);
lean_dec(v___x_278_);
v_snd_280_ = lean_ctor_get(v___x_279_, 1);
lean_inc(v_snd_280_);
return v_snd_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get___boxed(lean_object* v_00_u03b1_281_, lean_object* v_00_u03b2_282_, lean_object* v_inst_283_, lean_object* v_map_284_, lean_object* v_key_285_, lean_object* v_h_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_Internal_MultiMap_get(v_00_u03b1_281_, v_00_u03b2_282_, v_inst_283_, v_map_284_, v_key_285_, v_h_286_);
lean_dec_ref(v_map_284_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getAll_x3f___redArg(lean_object* v_inst_288_, lean_object* v_map_289_, lean_object* v_key_290_){
_start:
{
lean_object* v___y_292_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = ((lean_object*)(l_Std_Internal_MultiMap_getAll___redArg___closed__0));
v___x_300_ = lean_array_get_size(v_map_289_);
v___x_301_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_302_ = lean_nat_dec_lt(v___x_298_, v___x_300_);
if (v___x_302_ == 0)
{
lean_dec(v_key_290_);
lean_dec_ref(v_map_289_);
lean_dec_ref(v_inst_288_);
v___y_292_ = v___x_299_;
goto v___jp_291_;
}
else
{
lean_object* v___f_303_; size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; 
v___f_303_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_getAll___redArg___lam__0), 4, 2);
lean_closure_set(v___f_303_, 0, v_inst_288_);
lean_closure_set(v___f_303_, 1, v_key_290_);
v___x_304_ = ((size_t)0ULL);
v___x_305_ = lean_usize_of_nat(v___x_300_);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_301_, v___f_303_, v_map_289_, v___x_304_, v___x_305_, v___x_299_);
v___y_292_ = v___x_306_;
goto v___jp_291_;
}
v___jp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_293_ = lean_array_get_size(v___y_292_);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_nat_dec_eq(v___x_293_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_296_, 0, v___y_292_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; 
lean_dec_ref(v___y_292_);
v___x_297_ = lean_box(0);
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getAll_x3f(lean_object* v_00_u03b1_307_, lean_object* v_00_u03b2_308_, lean_object* v_inst_309_, lean_object* v_map_310_, lean_object* v_key_311_){
_start:
{
lean_object* v___y_313_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = ((lean_object*)(l_Std_Internal_MultiMap_getAll___redArg___closed__0));
v___x_321_ = lean_array_get_size(v_map_310_);
v___x_322_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_323_ = lean_nat_dec_lt(v___x_319_, v___x_321_);
if (v___x_323_ == 0)
{
lean_dec(v_key_311_);
lean_dec_ref(v_map_310_);
lean_dec_ref(v_inst_309_);
v___y_313_ = v___x_320_;
goto v___jp_312_;
}
else
{
lean_object* v___f_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; 
v___f_324_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_getAll___redArg___lam__0), 4, 2);
lean_closure_set(v___f_324_, 0, v_inst_309_);
lean_closure_set(v___f_324_, 1, v_key_311_);
v___x_325_ = ((size_t)0ULL);
v___x_326_ = lean_usize_of_nat(v___x_321_);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_322_, v___f_324_, v_map_310_, v___x_325_, v___x_326_, v___x_320_);
v___y_313_ = v___x_327_;
goto v___jp_312_;
}
v___jp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = lean_array_get_size(v___y_313_);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_nat_dec_eq(v___x_314_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v___y_313_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; 
lean_dec_ref(v___y_313_);
v___x_318_ = lean_box(0);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x3f___redArg(lean_object* v_inst_328_, lean_object* v_map_329_, lean_object* v_key_330_){
_start:
{
lean_object* v___x_331_; lean_object* v_i_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_331_ = lean_unsigned_to_nat(0u);
v_i_332_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v_inst_328_, v_map_329_, v_key_330_, v___x_331_);
v___x_333_ = lean_array_get_size(v_map_329_);
v___x_334_ = lean_nat_dec_lt(v_i_332_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec(v_i_332_);
v___x_335_ = lean_box(0);
return v___x_335_;
}
else
{
lean_object* v___x_336_; lean_object* v_snd_337_; lean_object* v___x_338_; 
v___x_336_ = lean_array_fget_borrowed(v_map_329_, v_i_332_);
lean_dec(v_i_332_);
v_snd_337_ = lean_ctor_get(v___x_336_, 1);
lean_inc(v_snd_337_);
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v_snd_337_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x3f___redArg___boxed(lean_object* v_inst_339_, lean_object* v_map_340_, lean_object* v_key_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_Internal_MultiMap_get_x3f___redArg(v_inst_339_, v_map_340_, v_key_341_);
lean_dec_ref(v_map_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x3f(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_inst_345_, lean_object* v_map_346_, lean_object* v_key_347_){
_start:
{
lean_object* v___x_348_; lean_object* v_i_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_348_ = lean_unsigned_to_nat(0u);
v_i_349_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v_inst_345_, v_map_346_, v_key_347_, v___x_348_);
v___x_350_ = lean_array_get_size(v_map_346_);
v___x_351_ = lean_nat_dec_lt(v_i_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_dec(v_i_349_);
v___x_352_ = lean_box(0);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v_snd_354_; lean_object* v___x_355_; 
v___x_353_ = lean_array_fget_borrowed(v_map_346_, v_i_349_);
lean_dec(v_i_349_);
v_snd_354_ = lean_ctor_get(v___x_353_, 1);
lean_inc(v_snd_354_);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v_snd_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x3f___boxed(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_inst_358_, lean_object* v_map_359_, lean_object* v_key_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_Internal_MultiMap_get_x3f(v_00_u03b1_356_, v_00_u03b2_357_, v_inst_358_, v_map_359_, v_key_360_);
lean_dec_ref(v_map_359_);
return v_res_361_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_hasEntry___redArg___lam__0(lean_object* v_inst_362_, lean_object* v_key_363_, lean_object* v_inst_364_, lean_object* v_value_365_, lean_object* v_x_366_){
_start:
{
lean_object* v_fst_367_; lean_object* v_snd_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_fst_367_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_fst_367_);
v_snd_368_ = lean_ctor_get(v_x_366_, 1);
lean_inc(v_snd_368_);
lean_dec_ref(v_x_366_);
v___x_369_ = lean_apply_2(v_inst_362_, v_fst_367_, v_key_363_);
v___x_370_ = lean_unbox(v___x_369_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; 
lean_dec(v_snd_368_);
lean_dec(v_value_365_);
lean_dec_ref(v_inst_364_);
v___x_371_ = lean_unbox(v___x_369_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_apply_2(v_inst_364_, v_snd_368_, v_value_365_);
v___x_373_ = lean_unbox(v___x_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_hasEntry___redArg___lam__0___boxed(lean_object* v_inst_374_, lean_object* v_key_375_, lean_object* v_inst_376_, lean_object* v_value_377_, lean_object* v_x_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = l_Std_Internal_MultiMap_hasEntry___redArg___lam__0(v_inst_374_, v_key_375_, v_inst_376_, v_value_377_, v_x_378_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_hasEntry___redArg(lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_map_383_, lean_object* v_key_384_, lean_object* v_value_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_array_get_size(v_map_383_);
v___x_388_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_389_ = lean_nat_dec_lt(v___x_386_, v___x_387_);
if (v___x_389_ == 0)
{
lean_dec(v_value_385_);
lean_dec(v_key_384_);
lean_dec_ref(v_map_383_);
lean_dec_ref(v_inst_382_);
lean_dec_ref(v_inst_381_);
return v___x_389_;
}
else
{
if (v___x_389_ == 0)
{
lean_dec(v_value_385_);
lean_dec(v_key_384_);
lean_dec_ref(v_map_383_);
lean_dec_ref(v_inst_382_);
lean_dec_ref(v_inst_381_);
return v___x_389_;
}
else
{
lean_object* v___f_390_; size_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___f_390_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_hasEntry___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_390_, 0, v_inst_381_);
lean_closure_set(v___f_390_, 1, v_key_384_);
lean_closure_set(v___f_390_, 2, v_inst_382_);
lean_closure_set(v___f_390_, 3, v_value_385_);
v___x_391_ = ((size_t)0ULL);
v___x_392_ = lean_usize_of_nat(v___x_387_);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_388_, v___f_390_, v_map_383_, v___x_391_, v___x_392_);
v___x_394_ = lean_unbox(v___x_393_);
lean_dec(v___x_393_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_hasEntry___redArg___boxed(lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_map_397_, lean_object* v_key_398_, lean_object* v_value_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Std_Internal_MultiMap_hasEntry___redArg(v_inst_395_, v_inst_396_, v_map_397_, v_key_398_, v_value_399_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_hasEntry(lean_object* v_00_u03b1_402_, lean_object* v_00_u03b2_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_map_406_, lean_object* v_key_407_, lean_object* v_value_408_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = lean_array_get_size(v_map_406_);
v___x_411_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_412_ = lean_nat_dec_lt(v___x_409_, v___x_410_);
if (v___x_412_ == 0)
{
lean_dec(v_value_408_);
lean_dec(v_key_407_);
lean_dec_ref(v_map_406_);
lean_dec_ref(v_inst_405_);
lean_dec_ref(v_inst_404_);
return v___x_412_;
}
else
{
if (v___x_412_ == 0)
{
lean_dec(v_value_408_);
lean_dec(v_key_407_);
lean_dec_ref(v_map_406_);
lean_dec_ref(v_inst_405_);
lean_dec_ref(v_inst_404_);
return v___x_412_;
}
else
{
lean_object* v___f_413_; size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___f_413_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_hasEntry___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_413_, 0, v_inst_404_);
lean_closure_set(v___f_413_, 1, v_key_407_);
lean_closure_set(v___f_413_, 2, v_inst_405_);
lean_closure_set(v___f_413_, 3, v_value_408_);
v___x_414_ = ((size_t)0ULL);
v___x_415_ = lean_usize_of_nat(v___x_410_);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_411_, v___f_413_, v_map_406_, v___x_414_, v___x_415_);
v___x_417_ = lean_unbox(v___x_416_);
lean_dec(v___x_416_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_hasEntry___boxed(lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_map_422_, lean_object* v_key_423_, lean_object* v_value_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_Std_Internal_MultiMap_hasEntry(v_00_u03b1_418_, v_00_u03b2_419_, v_inst_420_, v_inst_421_, v_map_422_, v_key_423_, v_value_424_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getLast_x3f___redArg(lean_object* v_inst_427_, lean_object* v_map_428_, lean_object* v_key_429_){
_start:
{
lean_object* v___x_430_; lean_object* v_i_431_; uint8_t v___x_432_; 
v___x_430_ = lean_array_get_size(v_map_428_);
v_i_431_ = l_Std_Internal_MultiMap_findLastIdxBelow___redArg(v_inst_427_, v_map_428_, v_key_429_, v___x_430_);
v___x_432_ = lean_nat_dec_lt(v_i_431_, v___x_430_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec(v_i_431_);
v___x_433_ = lean_box(0);
return v___x_433_;
}
else
{
lean_object* v___x_434_; lean_object* v_snd_435_; lean_object* v___x_436_; 
v___x_434_ = lean_array_fget_borrowed(v_map_428_, v_i_431_);
lean_dec(v_i_431_);
v_snd_435_ = lean_ctor_get(v___x_434_, 1);
lean_inc(v_snd_435_);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v_snd_435_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getLast_x3f___redArg___boxed(lean_object* v_inst_437_, lean_object* v_map_438_, lean_object* v_key_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_Internal_MultiMap_getLast_x3f___redArg(v_inst_437_, v_map_438_, v_key_439_);
lean_dec_ref(v_map_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getLast_x3f(lean_object* v_00_u03b1_441_, lean_object* v_00_u03b2_442_, lean_object* v_inst_443_, lean_object* v_map_444_, lean_object* v_key_445_){
_start:
{
lean_object* v___x_446_; lean_object* v_i_447_; uint8_t v___x_448_; 
v___x_446_ = lean_array_get_size(v_map_444_);
v_i_447_ = l_Std_Internal_MultiMap_findLastIdxBelow___redArg(v_inst_443_, v_map_444_, v_key_445_, v___x_446_);
v___x_448_ = lean_nat_dec_lt(v_i_447_, v___x_446_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
lean_dec(v_i_447_);
v___x_449_ = lean_box(0);
return v___x_449_;
}
else
{
lean_object* v___x_450_; lean_object* v_snd_451_; lean_object* v___x_452_; 
v___x_450_ = lean_array_fget_borrowed(v_map_444_, v_i_447_);
lean_dec(v_i_447_);
v_snd_451_ = lean_ctor_get(v___x_450_, 1);
lean_inc(v_snd_451_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v_snd_451_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getLast_x3f___boxed(lean_object* v_00_u03b1_453_, lean_object* v_00_u03b2_454_, lean_object* v_inst_455_, lean_object* v_map_456_, lean_object* v_key_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_Internal_MultiMap_getLast_x3f(v_00_u03b1_453_, v_00_u03b2_454_, v_inst_455_, v_map_456_, v_key_457_);
lean_dec_ref(v_map_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getD___redArg(lean_object* v_inst_459_, lean_object* v_map_460_, lean_object* v_key_461_, lean_object* v_d_462_){
_start:
{
lean_object* v___x_463_; lean_object* v_i_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_463_ = lean_unsigned_to_nat(0u);
v_i_464_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v_inst_459_, v_map_460_, v_key_461_, v___x_463_);
v___x_465_ = lean_array_get_size(v_map_460_);
v___x_466_ = lean_nat_dec_lt(v_i_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_dec(v_i_464_);
lean_inc(v_d_462_);
return v_d_462_;
}
else
{
lean_object* v___x_467_; lean_object* v_snd_468_; 
v___x_467_ = lean_array_fget_borrowed(v_map_460_, v_i_464_);
lean_dec(v_i_464_);
v_snd_468_ = lean_ctor_get(v___x_467_, 1);
lean_inc(v_snd_468_);
return v_snd_468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getD___redArg___boxed(lean_object* v_inst_469_, lean_object* v_map_470_, lean_object* v_key_471_, lean_object* v_d_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Std_Internal_MultiMap_getD___redArg(v_inst_469_, v_map_470_, v_key_471_, v_d_472_);
lean_dec(v_d_472_);
lean_dec_ref(v_map_470_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getD(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_inst_476_, lean_object* v_map_477_, lean_object* v_key_478_, lean_object* v_d_479_){
_start:
{
lean_object* v___x_480_; lean_object* v_i_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_480_ = lean_unsigned_to_nat(0u);
v_i_481_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v_inst_476_, v_map_477_, v_key_478_, v___x_480_);
v___x_482_ = lean_array_get_size(v_map_477_);
v___x_483_ = lean_nat_dec_lt(v_i_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_dec(v_i_481_);
lean_inc(v_d_479_);
return v_d_479_;
}
else
{
lean_object* v___x_484_; lean_object* v_snd_485_; 
v___x_484_ = lean_array_fget_borrowed(v_map_477_, v_i_481_);
lean_dec(v_i_481_);
v_snd_485_ = lean_ctor_get(v___x_484_, 1);
lean_inc(v_snd_485_);
return v_snd_485_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_getD___boxed(lean_object* v_00_u03b1_486_, lean_object* v_00_u03b2_487_, lean_object* v_inst_488_, lean_object* v_map_489_, lean_object* v_key_490_, lean_object* v_d_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_Internal_MultiMap_getD(v_00_u03b1_486_, v_00_u03b2_487_, v_inst_488_, v_map_489_, v_key_490_, v_d_491_);
lean_dec(v_d_491_);
lean_dec_ref(v_map_489_);
return v_res_492_;
}
}
static lean_object* _init_l_Std_Internal_MultiMap_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_496_ = ((lean_object*)(l_Std_Internal_MultiMap_get_x21___redArg___closed__2));
v___x_497_ = lean_unsigned_to_nat(14u);
v___x_498_ = lean_unsigned_to_nat(22u);
v___x_499_ = ((lean_object*)(l_Std_Internal_MultiMap_get_x21___redArg___closed__1));
v___x_500_ = ((lean_object*)(l_Std_Internal_MultiMap_get_x21___redArg___closed__0));
v___x_501_ = l_mkPanicMessageWithDecl(v___x_500_, v___x_499_, v___x_498_, v___x_497_, v___x_496_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x21___redArg(lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_map_504_, lean_object* v_key_505_){
_start:
{
lean_object* v___x_506_; lean_object* v_i_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_506_ = lean_unsigned_to_nat(0u);
v_i_507_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v_inst_502_, v_map_504_, v_key_505_, v___x_506_);
v___x_508_ = lean_array_get_size(v_map_504_);
v___x_509_ = lean_nat_dec_lt(v_i_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_i_507_);
v___x_510_ = lean_obj_once(&l_Std_Internal_MultiMap_get_x21___redArg___closed__3, &l_Std_Internal_MultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_MultiMap_get_x21___redArg___closed__3);
v___x_511_ = l_panic___redArg(v_inst_503_, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; lean_object* v_snd_513_; 
v___x_512_ = lean_array_fget_borrowed(v_map_504_, v_i_507_);
lean_dec(v_i_507_);
v_snd_513_ = lean_ctor_get(v___x_512_, 1);
lean_inc(v_snd_513_);
return v_snd_513_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x21___redArg___boxed(lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_map_516_, lean_object* v_key_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_Internal_MultiMap_get_x21___redArg(v_inst_514_, v_inst_515_, v_map_516_, v_key_517_);
lean_dec_ref(v_map_516_);
lean_dec(v_inst_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x21(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_map_523_, lean_object* v_key_524_){
_start:
{
lean_object* v___x_525_; lean_object* v_i_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_525_ = lean_unsigned_to_nat(0u);
v_i_526_ = l_Std_Internal_MultiMap_findIdxFrom___redArg(v_inst_521_, v_map_523_, v_key_524_, v___x_525_);
v___x_527_ = lean_array_get_size(v_map_523_);
v___x_528_ = lean_nat_dec_lt(v_i_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_i_526_);
v___x_529_ = lean_obj_once(&l_Std_Internal_MultiMap_get_x21___redArg___closed__3, &l_Std_Internal_MultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_MultiMap_get_x21___redArg___closed__3);
v___x_530_ = l_panic___redArg(v_inst_522_, v___x_529_);
return v___x_530_;
}
else
{
lean_object* v___x_531_; lean_object* v_snd_532_; 
v___x_531_ = lean_array_fget_borrowed(v_map_523_, v_i_526_);
lean_dec(v_i_526_);
v_snd_532_ = lean_ctor_get(v___x_531_, 1);
lean_inc(v_snd_532_);
return v_snd_532_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_get_x21___boxed(lean_object* v_00_u03b1_533_, lean_object* v_00_u03b2_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_map_537_, lean_object* v_key_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Std_Internal_MultiMap_get_x21(v_00_u03b1_533_, v_00_u03b2_534_, v_inst_535_, v_inst_536_, v_map_537_, v_key_538_);
lean_dec_ref(v_map_537_);
lean_dec(v_inst_536_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_insert___redArg(lean_object* v_map_540_, lean_object* v_key_541_, lean_object* v_value_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v_key_541_);
lean_ctor_set(v___x_543_, 1, v_value_542_);
v___x_544_ = lean_array_push(v_map_540_, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_insert(lean_object* v_00_u03b1_545_, lean_object* v_00_u03b2_546_, lean_object* v_map_547_, lean_object* v_key_548_, lean_object* v_value_549_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v_key_548_);
lean_ctor_set(v___x_550_, 1, v_value_549_);
v___x_551_ = lean_array_push(v_map_547_, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_insertMany___redArg___lam__0(lean_object* v_key_552_, lean_object* v_x1_553_, lean_object* v_x2_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v_key_552_);
lean_ctor_set(v___x_555_, 1, v_x2_554_);
v___x_556_ = lean_array_push(v_x1_553_, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_insertMany___redArg(lean_object* v_map_557_, lean_object* v_key_558_, lean_object* v_values_559_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_array_get_size(v_values_559_);
v___x_562_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_563_ = lean_nat_dec_lt(v___x_560_, v___x_561_);
if (v___x_563_ == 0)
{
lean_dec_ref(v_values_559_);
lean_dec(v_key_558_);
return v_map_557_;
}
else
{
lean_object* v___f_564_; size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
v___f_564_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_564_, 0, v_key_558_);
v___x_565_ = ((size_t)0ULL);
v___x_566_ = lean_usize_of_nat(v___x_561_);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_562_, v___f_564_, v_values_559_, v___x_565_, v___x_566_, v_map_557_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_insertMany(lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_map_570_, lean_object* v_key_571_, lean_object* v_values_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_array_get_size(v_values_572_);
v___x_575_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_576_ = lean_nat_dec_lt(v___x_573_, v___x_574_);
if (v___x_576_ == 0)
{
lean_dec_ref(v_values_572_);
lean_dec(v_key_571_);
return v_map_570_;
}
else
{
lean_object* v___f_577_; size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; 
v___f_577_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_577_, 0, v_key_571_);
v___x_578_ = ((size_t)0ULL);
v___x_579_ = lean_usize_of_nat(v___x_574_);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_575_, v___f_577_, v_values_572_, v___x_578_, v___x_579_, v_map_570_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_empty___redArg(){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(8u);
v___x_583_ = lean_mk_empty_array_with_capacity(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_empty___redArg___boxed(lean_object* v___dummy_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_Internal_MultiMap_empty___redArg();
return v_res_585_;
}
}
static lean_object* _init_l_Std_Internal_MultiMap_empty___closed__0(void){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_Internal_MultiMap_empty___redArg();
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_empty(lean_object* v_00_u03b1_587_, lean_object* v_00_u03b2_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_Std_Internal_MultiMap_empty___closed__0, &l_Std_Internal_MultiMap_empty___closed__0_once, _init_l_Std_Internal_MultiMap_empty___closed__0);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_ofList___redArg(lean_object* v_pairs_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_array_mk(v_pairs_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_ofList(lean_object* v_00_u03b1_592_, lean_object* v_00_u03b2_593_, lean_object* v_pairs_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_array_mk(v_pairs_594_);
return v___x_595_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_contains___redArg(lean_object* v_inst_596_, lean_object* v_map_597_, lean_object* v_key_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_array_get_size(v_map_597_);
v___x_601_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_602_ = lean_nat_dec_lt(v___x_599_, v___x_600_);
if (v___x_602_ == 0)
{
lean_dec(v_key_598_);
lean_dec_ref(v_map_597_);
lean_dec_ref(v_inst_596_);
return v___x_602_;
}
else
{
if (v___x_602_ == 0)
{
lean_dec(v_key_598_);
lean_dec_ref(v_map_597_);
lean_dec_ref(v_inst_596_);
return v___x_602_;
}
else
{
lean_object* v___f_603_; size_t v___x_604_; size_t v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___f_603_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_603_, 0, v_inst_596_);
lean_closure_set(v___f_603_, 1, v_key_598_);
v___x_604_ = ((size_t)0ULL);
v___x_605_ = lean_usize_of_nat(v___x_600_);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_601_, v___f_603_, v_map_597_, v___x_604_, v___x_605_);
v___x_607_ = lean_unbox(v___x_606_);
lean_dec(v___x_606_);
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_contains___redArg___boxed(lean_object* v_inst_608_, lean_object* v_map_609_, lean_object* v_key_610_){
_start:
{
uint8_t v_res_611_; lean_object* v_r_612_; 
v_res_611_ = l_Std_Internal_MultiMap_contains___redArg(v_inst_608_, v_map_609_, v_key_610_);
v_r_612_ = lean_box(v_res_611_);
return v_r_612_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_contains(lean_object* v_00_u03b1_613_, lean_object* v_00_u03b2_614_, lean_object* v_inst_615_, lean_object* v_map_616_, lean_object* v_key_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_array_get_size(v_map_616_);
v___x_620_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_621_ = lean_nat_dec_lt(v___x_618_, v___x_619_);
if (v___x_621_ == 0)
{
lean_dec(v_key_617_);
lean_dec_ref(v_map_616_);
lean_dec_ref(v_inst_615_);
return v___x_621_;
}
else
{
if (v___x_621_ == 0)
{
lean_dec(v_key_617_);
lean_dec_ref(v_map_616_);
lean_dec_ref(v_inst_615_);
return v___x_621_;
}
else
{
lean_object* v___f_622_; size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___f_622_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_622_, 0, v_inst_615_);
lean_closure_set(v___f_622_, 1, v_key_617_);
v___x_623_ = ((size_t)0ULL);
v___x_624_ = lean_usize_of_nat(v___x_619_);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_620_, v___f_622_, v_map_616_, v___x_623_, v___x_624_);
v___x_626_ = lean_unbox(v___x_625_);
lean_dec(v___x_625_);
return v___x_626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_contains___boxed(lean_object* v_00_u03b1_627_, lean_object* v_00_u03b2_628_, lean_object* v_inst_629_, lean_object* v_map_630_, lean_object* v_key_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l_Std_Internal_MultiMap_contains(v_00_u03b1_627_, v_00_u03b2_628_, v_inst_629_, v_map_630_, v_key_631_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_update___redArg___lam__1(lean_object* v_inst_634_, lean_object* v_key_635_, lean_object* v_f_636_, lean_object* v_x_637_){
_start:
{
lean_object* v_fst_638_; lean_object* v_snd_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_fst_638_ = lean_ctor_get(v_x_637_, 0);
v_snd_639_ = lean_ctor_get(v_x_637_, 1);
lean_inc(v_fst_638_);
v___x_640_ = lean_apply_2(v_inst_634_, v_fst_638_, v_key_635_);
v___x_641_ = lean_unbox(v___x_640_);
if (v___x_641_ == 0)
{
lean_dec(v_f_636_);
return v_x_637_;
}
else
{
lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_649_; 
lean_inc(v_snd_639_);
lean_inc(v_fst_638_);
v_isSharedCheck_649_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; lean_object* v_unused_651_; 
v_unused_650_ = lean_ctor_get(v_x_637_, 1);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_x_637_, 0);
lean_dec(v_unused_651_);
v___x_643_ = v_x_637_;
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
else
{
lean_dec(v_x_637_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = lean_apply_1(v_f_636_, v_snd_639_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_fst_638_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_update___redArg(lean_object* v_inst_652_, lean_object* v_map_653_, lean_object* v_key_654_, lean_object* v_f_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_array_get_size(v_map_653_);
v___x_658_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_659_ = lean_nat_dec_lt(v___x_656_, v___x_657_);
if (v___x_659_ == 0)
{
lean_dec(v_f_655_);
lean_dec(v_key_654_);
lean_dec_ref(v_inst_652_);
return v_map_653_;
}
else
{
lean_object* v___f_660_; size_t v___x_661_; size_t v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
lean_inc(v_key_654_);
lean_inc_ref(v_inst_652_);
v___f_660_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_660_, 0, v_inst_652_);
lean_closure_set(v___f_660_, 1, v_key_654_);
v___x_661_ = ((size_t)0ULL);
v___x_662_ = lean_usize_of_nat(v___x_657_);
lean_inc_ref(v_map_653_);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_658_, v___f_660_, v_map_653_, v___x_661_, v___x_662_);
v___x_664_ = lean_unbox(v___x_663_);
lean_dec(v___x_663_);
if (v___x_664_ == 0)
{
lean_dec(v_f_655_);
lean_dec(v_key_654_);
lean_dec_ref(v_inst_652_);
return v_map_653_;
}
else
{
lean_object* v___f_665_; size_t v_sz_666_; lean_object* v___x_667_; 
v___f_665_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_update___redArg___lam__1), 4, 3);
lean_closure_set(v___f_665_, 0, v_inst_652_);
lean_closure_set(v___f_665_, 1, v_key_654_);
lean_closure_set(v___f_665_, 2, v_f_655_);
v_sz_666_ = lean_array_size(v_map_653_);
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_658_, v___f_665_, v_sz_666_, v___x_661_, v_map_653_);
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_update(lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_inst_670_, lean_object* v_map_671_, lean_object* v_key_672_, lean_object* v_f_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_array_get_size(v_map_671_);
v___x_676_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_677_ = lean_nat_dec_lt(v___x_674_, v___x_675_);
if (v___x_677_ == 0)
{
lean_dec(v_f_673_);
lean_dec(v_key_672_);
lean_dec_ref(v_inst_670_);
return v_map_671_;
}
else
{
lean_object* v___f_678_; size_t v___x_679_; size_t v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
lean_inc(v_key_672_);
lean_inc_ref(v_inst_670_);
v___f_678_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_678_, 0, v_inst_670_);
lean_closure_set(v___f_678_, 1, v_key_672_);
v___x_679_ = ((size_t)0ULL);
v___x_680_ = lean_usize_of_nat(v___x_675_);
lean_inc_ref(v_map_671_);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_676_, v___f_678_, v_map_671_, v___x_679_, v___x_680_);
v___x_682_ = lean_unbox(v___x_681_);
lean_dec(v___x_681_);
if (v___x_682_ == 0)
{
lean_dec(v_f_673_);
lean_dec(v_key_672_);
lean_dec_ref(v_inst_670_);
return v_map_671_;
}
else
{
lean_object* v___f_683_; size_t v_sz_684_; lean_object* v___x_685_; 
v___f_683_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_update___redArg___lam__1), 4, 3);
lean_closure_set(v___f_683_, 0, v_inst_670_);
lean_closure_set(v___f_683_, 1, v_key_672_);
lean_closure_set(v___f_683_, 2, v_f_673_);
v_sz_684_ = lean_array_size(v_map_671_);
v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_676_, v___f_683_, v_sz_684_, v___x_679_, v_map_671_);
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_replaceLast___redArg(lean_object* v_inst_686_, lean_object* v_map_687_, lean_object* v_key_688_, lean_object* v_value_689_){
_start:
{
lean_object* v___x_690_; lean_object* v_i_691_; uint8_t v___x_692_; 
v___x_690_ = lean_array_get_size(v_map_687_);
lean_inc(v_key_688_);
v_i_691_ = l_Std_Internal_MultiMap_findLastIdxBelow___redArg(v_inst_686_, v_map_687_, v_key_688_, v___x_690_);
v___x_692_ = lean_nat_dec_lt(v_i_691_, v___x_690_);
if (v___x_692_ == 0)
{
lean_dec(v_i_691_);
lean_dec(v_value_689_);
lean_dec(v_key_688_);
return v_map_687_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_key_688_);
lean_ctor_set(v___x_693_, 1, v_value_689_);
v___x_694_ = lean_array_fset(v_map_687_, v_i_691_, v___x_693_);
lean_dec(v_i_691_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_replaceLast(lean_object* v_00_u03b1_695_, lean_object* v_00_u03b2_696_, lean_object* v_inst_697_, lean_object* v_map_698_, lean_object* v_key_699_, lean_object* v_value_700_){
_start:
{
lean_object* v___x_701_; lean_object* v_i_702_; uint8_t v___x_703_; 
v___x_701_ = lean_array_get_size(v_map_698_);
lean_inc(v_key_699_);
v_i_702_ = l_Std_Internal_MultiMap_findLastIdxBelow___redArg(v_inst_697_, v_map_698_, v_key_699_, v___x_701_);
v___x_703_ = lean_nat_dec_lt(v_i_702_, v___x_701_);
if (v___x_703_ == 0)
{
lean_dec(v_i_702_);
lean_dec(v_value_700_);
lean_dec(v_key_699_);
return v_map_698_;
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_key_699_);
lean_ctor_set(v___x_704_, 1, v_value_700_);
v___x_705_ = lean_array_fset(v_map_698_, v_i_702_, v___x_704_);
lean_dec(v_i_702_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_erase___redArg___lam__1(lean_object* v_inst_706_, lean_object* v_key_707_, lean_object* v_x1_708_, lean_object* v_x2_709_){
_start:
{
lean_object* v_fst_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_fst_710_ = lean_ctor_get(v_x2_709_, 0);
lean_inc(v_fst_710_);
v___x_711_ = lean_apply_2(v_inst_706_, v_fst_710_, v_key_707_);
v___x_712_ = lean_unbox(v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
v___x_713_ = lean_array_push(v_x1_708_, v_x2_709_);
return v___x_713_;
}
else
{
lean_dec_ref(v_x2_709_);
return v_x1_708_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_erase___redArg(lean_object* v_inst_716_, lean_object* v_map_717_, lean_object* v_key_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_array_get_size(v_map_717_);
v___x_721_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_722_ = lean_nat_dec_lt(v___x_719_, v___x_720_);
if (v___x_722_ == 0)
{
lean_dec(v_key_718_);
lean_dec_ref(v_inst_716_);
return v_map_717_;
}
else
{
lean_object* v___f_723_; size_t v___x_724_; size_t v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
lean_inc(v_key_718_);
lean_inc_ref(v_inst_716_);
v___f_723_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_723_, 0, v_inst_716_);
lean_closure_set(v___f_723_, 1, v_key_718_);
v___x_724_ = ((size_t)0ULL);
v___x_725_ = lean_usize_of_nat(v___x_720_);
lean_inc_ref(v_map_717_);
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_721_, v___f_723_, v_map_717_, v___x_724_, v___x_725_);
v___x_727_ = lean_unbox(v___x_726_);
lean_dec(v___x_726_);
if (v___x_727_ == 0)
{
lean_dec(v_key_718_);
lean_dec_ref(v_inst_716_);
return v_map_717_;
}
else
{
lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___f_728_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_728_, 0, v_inst_716_);
lean_closure_set(v___f_728_, 1, v_key_718_);
v___x_729_ = ((lean_object*)(l_Std_Internal_MultiMap_erase___redArg___closed__0));
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_721_, v___f_728_, v_map_717_, v___x_724_, v___x_725_, v___x_729_);
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_erase(lean_object* v_00_u03b1_731_, lean_object* v_00_u03b2_732_, lean_object* v_inst_733_, lean_object* v_map_734_, lean_object* v_key_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_array_get_size(v_map_734_);
v___x_738_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_739_ = lean_nat_dec_lt(v___x_736_, v___x_737_);
if (v___x_739_ == 0)
{
lean_dec(v_key_735_);
lean_dec_ref(v_inst_733_);
return v_map_734_;
}
else
{
lean_object* v___f_740_; size_t v___x_741_; size_t v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
lean_inc(v_key_735_);
lean_inc_ref(v_inst_733_);
v___f_740_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_740_, 0, v_inst_733_);
lean_closure_set(v___f_740_, 1, v_key_735_);
v___x_741_ = ((size_t)0ULL);
v___x_742_ = lean_usize_of_nat(v___x_737_);
lean_inc_ref(v_map_734_);
v___x_743_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_738_, v___f_740_, v_map_734_, v___x_741_, v___x_742_);
v___x_744_ = lean_unbox(v___x_743_);
lean_dec(v___x_743_);
if (v___x_744_ == 0)
{
lean_dec(v_key_735_);
lean_dec_ref(v_inst_733_);
return v_map_734_;
}
else
{
lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___f_745_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_745_, 0, v_inst_733_);
lean_closure_set(v___f_745_, 1, v_key_735_);
v___x_746_ = ((lean_object*)(l_Std_Internal_MultiMap_erase___redArg___closed__0));
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_738_, v___f_745_, v_map_734_, v___x_741_, v___x_742_, v___x_746_);
return v___x_747_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_eraseMany___redArg___lam__0(lean_object* v_inst_748_, lean_object* v_keys_749_, lean_object* v_x_750_){
_start:
{
lean_object* v_fst_751_; uint8_t v___x_752_; 
v_fst_751_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_fst_751_);
lean_dec_ref(v_x_750_);
v___x_752_ = l_Array_contains___redArg(v_inst_748_, v_keys_749_, v_fst_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_eraseMany___redArg___lam__0___boxed(lean_object* v_inst_753_, lean_object* v_keys_754_, lean_object* v_x_755_){
_start:
{
uint8_t v_res_756_; lean_object* v_r_757_; 
v_res_756_ = l_Std_Internal_MultiMap_eraseMany___redArg___lam__0(v_inst_753_, v_keys_754_, v_x_755_);
v_r_757_ = lean_box(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_eraseMany___redArg___lam__1(lean_object* v_inst_758_, lean_object* v_keys_759_, lean_object* v_x1_760_, lean_object* v_x2_761_){
_start:
{
lean_object* v_fst_762_; uint8_t v___x_763_; 
v_fst_762_ = lean_ctor_get(v_x2_761_, 0);
lean_inc(v_fst_762_);
v___x_763_ = l_Array_contains___redArg(v_inst_758_, v_keys_759_, v_fst_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
v___x_764_ = lean_array_push(v_x1_760_, v_x2_761_);
return v___x_764_;
}
else
{
lean_dec_ref(v_x2_761_);
return v_x1_760_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_eraseMany___redArg(lean_object* v_inst_765_, lean_object* v_map_766_, lean_object* v_keys_767_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_array_get_size(v_map_766_);
v___x_770_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_771_ = lean_nat_dec_lt(v___x_768_, v___x_769_);
if (v___x_771_ == 0)
{
lean_dec_ref(v_keys_767_);
lean_dec_ref(v_inst_765_);
return v_map_766_;
}
else
{
if (v___x_771_ == 0)
{
lean_dec_ref(v_keys_767_);
lean_dec_ref(v_inst_765_);
return v_map_766_;
}
else
{
lean_object* v___f_772_; size_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
lean_inc_ref(v_keys_767_);
lean_inc_ref(v_inst_765_);
v___f_772_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_eraseMany___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_772_, 0, v_inst_765_);
lean_closure_set(v___f_772_, 1, v_keys_767_);
v___x_773_ = ((size_t)0ULL);
v___x_774_ = lean_usize_of_nat(v___x_769_);
lean_inc_ref(v_map_766_);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_770_, v___f_772_, v_map_766_, v___x_773_, v___x_774_);
v___x_776_ = lean_unbox(v___x_775_);
lean_dec(v___x_775_);
if (v___x_776_ == 0)
{
lean_dec_ref(v_keys_767_);
lean_dec_ref(v_inst_765_);
return v_map_766_;
}
else
{
lean_object* v___x_777_; 
v___x_777_ = ((lean_object*)(l_Std_Internal_MultiMap_erase___redArg___closed__0));
if (v___x_771_ == 0)
{
lean_dec_ref(v_keys_767_);
lean_dec_ref(v_map_766_);
lean_dec_ref(v_inst_765_);
return v___x_777_;
}
else
{
lean_object* v___f_778_; lean_object* v___x_779_; 
v___f_778_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_eraseMany___redArg___lam__1), 4, 2);
lean_closure_set(v___f_778_, 0, v_inst_765_);
lean_closure_set(v___f_778_, 1, v_keys_767_);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_770_, v___f_778_, v_map_766_, v___x_773_, v___x_774_, v___x_777_);
return v___x_779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_eraseMany(lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v_inst_782_, lean_object* v_map_783_, lean_object* v_keys_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = lean_array_get_size(v_map_783_);
v___x_787_ = ((lean_object*)(l_Std_Internal_MultiMap_instDecidableMem___redArg___closed__9));
v___x_788_ = lean_nat_dec_lt(v___x_785_, v___x_786_);
if (v___x_788_ == 0)
{
lean_dec_ref(v_keys_784_);
lean_dec_ref(v_inst_782_);
return v_map_783_;
}
else
{
if (v___x_788_ == 0)
{
lean_dec_ref(v_keys_784_);
lean_dec_ref(v_inst_782_);
return v_map_783_;
}
else
{
lean_object* v___f_789_; size_t v___x_790_; size_t v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
lean_inc_ref(v_keys_784_);
lean_inc_ref(v_inst_782_);
v___f_789_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_eraseMany___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_789_, 0, v_inst_782_);
lean_closure_set(v___f_789_, 1, v_keys_784_);
v___x_790_ = ((size_t)0ULL);
v___x_791_ = lean_usize_of_nat(v___x_786_);
lean_inc_ref(v_map_783_);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_787_, v___f_789_, v_map_783_, v___x_790_, v___x_791_);
v___x_793_ = lean_unbox(v___x_792_);
lean_dec(v___x_792_);
if (v___x_793_ == 0)
{
lean_dec_ref(v_keys_784_);
lean_dec_ref(v_inst_782_);
return v_map_783_;
}
else
{
lean_object* v___x_794_; 
v___x_794_ = ((lean_object*)(l_Std_Internal_MultiMap_erase___redArg___closed__0));
if (v___x_788_ == 0)
{
lean_dec_ref(v_keys_784_);
lean_dec_ref(v_map_783_);
lean_dec_ref(v_inst_782_);
return v___x_794_;
}
else
{
lean_object* v___f_795_; lean_object* v___x_796_; 
v___f_795_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_eraseMany___redArg___lam__1), 4, 2);
lean_closure_set(v___f_795_, 0, v_inst_782_);
lean_closure_set(v___f_795_, 1, v_keys_784_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_787_, v___f_795_, v_map_783_, v___x_790_, v___x_791_, v___x_794_);
return v___x_796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_size___redArg(lean_object* v_map_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = lean_array_get_size(v_map_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_size___redArg___boxed(lean_object* v_map_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_Internal_MultiMap_size___redArg(v_map_799_);
lean_dec_ref(v_map_799_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_size(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_map_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = lean_array_get_size(v_map_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_size___boxed(lean_object* v_00_u03b1_805_, lean_object* v_00_u03b2_806_, lean_object* v_map_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_Internal_MultiMap_size(v_00_u03b1_805_, v_00_u03b2_806_, v_map_807_);
lean_dec_ref(v_map_807_);
return v_res_808_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_isEmpty___redArg(lean_object* v_map_809_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_810_ = lean_array_get_size(v_map_809_);
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = lean_nat_dec_eq(v___x_810_, v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_isEmpty___redArg___boxed(lean_object* v_map_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l_Std_Internal_MultiMap_isEmpty___redArg(v_map_813_);
lean_dec_ref(v_map_813_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_MultiMap_isEmpty(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_map_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_819_ = lean_array_get_size(v_map_818_);
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = lean_nat_dec_eq(v___x_819_, v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_isEmpty___boxed(lean_object* v_00_u03b1_822_, lean_object* v_00_u03b2_823_, lean_object* v_map_824_){
_start:
{
uint8_t v_res_825_; lean_object* v_r_826_; 
v_res_825_ = l_Std_Internal_MultiMap_isEmpty(v_00_u03b1_822_, v_00_u03b2_823_, v_map_824_);
lean_dec_ref(v_map_824_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_toArray___redArg(lean_object* v_map_827_){
_start:
{
lean_inc_ref(v_map_827_);
return v_map_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_toArray___redArg___boxed(lean_object* v_map_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_Internal_MultiMap_toArray___redArg(v_map_828_);
lean_dec_ref(v_map_828_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_toArray(lean_object* v_00_u03b1_830_, lean_object* v_00_u03b2_831_, lean_object* v_map_832_){
_start:
{
lean_inc_ref(v_map_832_);
return v_map_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_toArray___boxed(lean_object* v_00_u03b1_833_, lean_object* v_00_u03b2_834_, lean_object* v_map_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_Internal_MultiMap_toArray(v_00_u03b1_833_, v_00_u03b2_834_, v_map_835_);
lean_dec_ref(v_map_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_toList___redArg(lean_object* v_map_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = lean_array_to_list(v_map_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_toList(lean_object* v_00_u03b1_839_, lean_object* v_00_u03b2_840_, lean_object* v_map_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_array_to_list(v_map_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_merge___redArg(lean_object* v_m1_843_, lean_object* v_m2_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Array_append___redArg(v_m1_843_, v_m2_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_merge___redArg___boxed(lean_object* v_m1_846_, lean_object* v_m2_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_Internal_MultiMap_merge___redArg(v_m1_846_, v_m2_847_);
lean_dec_ref(v_m2_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_merge(lean_object* v_00_u03b1_849_, lean_object* v_00_u03b2_850_, lean_object* v_m1_851_, lean_object* v_m2_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Array_append___redArg(v_m1_851_, v_m2_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_merge___boxed(lean_object* v_00_u03b1_854_, lean_object* v_00_u03b2_855_, lean_object* v_m1_856_, lean_object* v_m2_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_Internal_MultiMap_merge(v_00_u03b1_854_, v_00_u03b2_855_, v_m1_856_, v_m2_857_);
lean_dec_ref(v_m2_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = lean_obj_once(&l_Std_Internal_MultiMap_empty___closed__0, &l_Std_Internal_MultiMap_empty___closed__0_once, _init_l_Std_Internal_MultiMap_empty___closed__0);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_Internal_MultiMap_instEmptyCollection___redArg();
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instEmptyCollection(lean_object* v_00_u03b1_863_, lean_object* v_00_u03b2_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = lean_obj_once(&l_Std_Internal_MultiMap_empty___closed__0, &l_Std_Internal_MultiMap_empty___closed__0_once, _init_l_Std_Internal_MultiMap_empty___closed__0);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instSingletonProd___redArg___lam__0(lean_object* v_x_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_obj_once(&l_Std_Internal_MultiMap_empty___closed__0, &l_Std_Internal_MultiMap_empty___closed__0_once, _init_l_Std_Internal_MultiMap_empty___closed__0);
v___x_868_ = lean_array_push(v___x_867_, v_x_866_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instSingletonProd___redArg(){
_start:
{
lean_object* v___f_871_; 
v___f_871_ = ((lean_object*)(l_Std_Internal_MultiMap_instSingletonProd___redArg___closed__0));
return v___f_871_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instSingletonProd___redArg___boxed(lean_object* v___dummy_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_Internal_MultiMap_instSingletonProd___redArg();
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instSingletonProd(lean_object* v_00_u03b1_874_, lean_object* v_00_u03b2_875_){
_start:
{
lean_object* v___f_876_; 
v___f_876_ = ((lean_object*)(l_Std_Internal_MultiMap_instSingletonProd___redArg___closed__0));
return v___f_876_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instInsertProd___redArg___lam__0(lean_object* v_x_877_, lean_object* v_m_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = lean_array_push(v_m_878_, v_x_877_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instInsertProd___redArg(){
_start:
{
lean_object* v___f_882_; 
v___f_882_ = ((lean_object*)(l_Std_Internal_MultiMap_instInsertProd___redArg___closed__0));
return v___f_882_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instInsertProd___redArg___boxed(lean_object* v___dummy_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_Internal_MultiMap_instInsertProd___redArg();
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instInsertProd(lean_object* v_00_u03b1_885_, lean_object* v_00_u03b2_886_){
_start:
{
lean_object* v___f_887_; 
v___f_887_ = ((lean_object*)(l_Std_Internal_MultiMap_instInsertProd___redArg___closed__0));
return v___f_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instUnion___redArg(){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = ((lean_object*)(l_Std_Internal_MultiMap_instUnion___redArg___closed__0));
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instUnion___redArg___boxed(lean_object* v___dummy_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_Internal_MultiMap_instUnion___redArg();
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instUnion(lean_object* v_00_u03b1_893_, lean_object* v_00_u03b2_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = ((lean_object*)(l_Std_Internal_MultiMap_instUnion___redArg___closed__0));
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_896_, lean_object* v_a_897_, lean_object* v_x_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_apply_2(v_f_896_, v_a_897_, v___y_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_901_, lean_object* v_00_u03b2_902_, lean_object* v_map_903_, lean_object* v_b_904_, lean_object* v_f_905_){
_start:
{
lean_object* v___f_906_; size_t v_sz_907_; size_t v___x_908_; lean_object* v___x_909_; 
v___f_906_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_906_, 0, v_f_905_);
v_sz_907_ = lean_array_size(v_map_903_);
v___x_908_ = ((size_t)0ULL);
v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_901_, v_map_903_, v___f_906_, v_sz_907_, v___x_908_, v_b_904_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instForInProdOfMonad___redArg(lean_object* v_inst_910_){
_start:
{
lean_object* v___f_911_; 
v___f_911_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_911_, 0, v_inst_910_);
return v___f_911_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_instForInProdOfMonad(lean_object* v_00_u03b1_912_, lean_object* v_00_u03b2_913_, lean_object* v_m_914_, lean_object* v_inst_915_){
_start:
{
lean_object* v___f_916_; 
v___f_916_ = lean_alloc_closure((void*)(l_Std_Internal_MultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_916_, 0, v_inst_915_);
return v___f_916_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Internal_MultiMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Internal_MultiMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Internal_MultiMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal_MultiMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Internal_MultiMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Internal_MultiMap(builtin);
}
#ifdef __cplusplus
}
#endif
