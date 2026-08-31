// Lean compiler output
// Module: Std.Sat.CNF.Basic
// Imports: public import Std.Sat.CNF.Literal public import Init.Data.Prod public import Init.Data.Array.Lemmas import Init.Data.Array.Bootstrap import Init.Data.List.Range import Init.Data.List.Nat.Range import Init.Data.ByteArray.Lemmas import Init.Data.List.Sublist import Init.Data.List.TakeDrop import Init.Omega import Init.ByCases
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
extern lean_object* l_ByteArray_empty;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_byte_array_uget(lean_object*, size_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t l_Array_instDecidableEqImpl___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_sarray_dec_eq(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_zipIdx___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Sat_CNF_Clause_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_CNF_Clause_empty___closed__0 = (const lean_object*)&l_Std_Sat_CNF_Clause_empty___closed__0_value;
static lean_once_cell_t l_Std_Sat_CNF_Clause_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_CNF_Clause_empty___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_polarity___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_polarity___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_polarity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_polarity___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_literals___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_literals(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_ofLiterals___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_ofLiterals(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instMembershipLiteral(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_contains(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0(lean_object*, size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_forIn_x27ImplUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_forIn_x27ImplUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_append(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Sat_CNF_Clause_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Sat_CNF_Clause_append, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Sat_CNF_Clause_instAppend___closed__0 = (const lean_object*)&l_Std_Sat_CNF_Clause_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instAppend(lean_object*);
static const lean_array_object l_Std_Sat_CNF_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_CNF_empty___closed__0 = (const lean_object*)&l_Std_Sat_CNF_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Sat_CNF_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Sat_CNF_append___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Sat_CNF_instAppend___closed__0 = (const lean_object*)&l_Std_Sat_CNF_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__0 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__0_value;
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__1 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__1_value;
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__2 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__2_value;
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__3 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__3_value;
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__4 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__4_value;
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__5 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__5_value;
static const lean_closure_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__6 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__6_value;
static const lean_ctor_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__0_value),((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__1_value)}};
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__7 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__7_value;
static const lean_ctor_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__7_value),((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__2_value),((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__3_value),((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__4_value),((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__5_value)}};
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__8 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__8_value;
static const lean_ctor_object l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__8_value),((lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__6_value)}};
static const lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9 = (const lean_object*)&l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9_value;
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableEq___redArg(lean_object* v_inst_1_, lean_object* v_c1_2_, lean_object* v_c2_3_){
_start:
{
lean_object* v_atoms_4_; lean_object* v_polarities_5_; lean_object* v_atoms_6_; lean_object* v_polarities_7_; uint8_t v___x_8_; 
v_atoms_4_ = lean_ctor_get(v_c1_2_, 0);
v_polarities_5_ = lean_ctor_get(v_c1_2_, 1);
v_atoms_6_ = lean_ctor_get(v_c2_3_, 0);
v_polarities_7_ = lean_ctor_get(v_c2_3_, 1);
v___x_8_ = l_Array_instDecidableEqImpl___redArg(v_inst_1_, v_atoms_4_, v_atoms_6_);
if (v___x_8_ == 0)
{
return v___x_8_;
}
else
{
uint8_t v___x_9_; 
v___x_9_ = lean_sarray_dec_eq(v_polarities_5_, v_polarities_7_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableEq___redArg___boxed(lean_object* v_inst_10_, lean_object* v_c1_11_, lean_object* v_c2_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_Sat_CNF_Clause_instDecidableEq___redArg(v_inst_10_, v_c1_11_, v_c2_12_);
lean_dec_ref(v_c2_12_);
lean_dec_ref(v_c1_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableEq(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_c1_17_, lean_object* v_c2_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = l_Std_Sat_CNF_Clause_instDecidableEq___redArg(v_inst_16_, v_c1_17_, v_c2_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableEq___boxed(lean_object* v_00_u03b1_20_, lean_object* v_inst_21_, lean_object* v_c1_22_, lean_object* v_c2_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Std_Sat_CNF_Clause_instDecidableEq(v_00_u03b1_20_, v_inst_21_, v_c1_22_, v_c2_23_);
lean_dec_ref(v_c2_23_);
lean_dec_ref(v_c1_22_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
static lean_object* _init_l_Std_Sat_CNF_Clause_empty___closed__1(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = l_ByteArray_empty;
v___x_29_ = ((lean_object*)(l_Std_Sat_CNF_Clause_empty___closed__0));
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_empty(lean_object* v_00_u03b1_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___closed__1, &l_Std_Sat_CNF_Clause_empty___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___closed__1);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instInhabited(lean_object* v_00_u03b1_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___closed__1, &l_Std_Sat_CNF_Clause_empty___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___closed__1);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size___redArg(lean_object* v_c_35_){
_start:
{
lean_object* v_atoms_36_; lean_object* v___x_37_; 
v_atoms_36_ = lean_ctor_get(v_c_35_, 0);
v___x_37_ = lean_array_get_size(v_atoms_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size___redArg___boxed(lean_object* v_c_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_Sat_CNF_Clause_size___redArg(v_c_38_);
lean_dec_ref(v_c_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size(lean_object* v_00_u03b1_40_, lean_object* v_c_41_){
_start:
{
lean_object* v_atoms_42_; lean_object* v___x_43_; 
v_atoms_42_ = lean_ctor_get(v_c_41_, 0);
v___x_43_ = lean_array_get_size(v_atoms_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size___boxed(lean_object* v_00_u03b1_44_, lean_object* v_c_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_Sat_CNF_Clause_size(v_00_u03b1_44_, v_c_45_);
lean_dec_ref(v_c_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add___redArg(lean_object* v_c_47_, lean_object* v_atom_48_, uint8_t v_pol_49_){
_start:
{
lean_object* v_atoms_50_; lean_object* v_polarities_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_64_; 
v_atoms_50_ = lean_ctor_get(v_c_47_, 0);
v_polarities_51_ = lean_ctor_get(v_c_47_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_c_47_);
if (v_isSharedCheck_64_ == 0)
{
v___x_53_ = v_c_47_;
v_isShared_54_ = v_isSharedCheck_64_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_polarities_51_);
lean_inc(v_atoms_50_);
lean_dec(v_c_47_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_64_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; uint8_t v___y_57_; 
v___x_55_ = lean_array_push(v_atoms_50_, v_atom_48_);
if (v_pol_49_ == 0)
{
uint8_t v___x_62_; 
v___x_62_ = 0;
v___y_57_ = v___x_62_;
goto v___jp_56_;
}
else
{
uint8_t v___x_63_; 
v___x_63_ = 1;
v___y_57_ = v___x_63_;
goto v___jp_56_;
}
v___jp_56_:
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = lean_byte_array_push(v_polarities_51_, v___y_57_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v___x_58_);
lean_ctor_set(v___x_53_, 0, v___x_55_);
v___x_60_ = v___x_53_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add___redArg___boxed(lean_object* v_c_65_, lean_object* v_atom_66_, lean_object* v_pol_67_){
_start:
{
uint8_t v_pol_boxed_68_; lean_object* v_res_69_; 
v_pol_boxed_68_ = lean_unbox(v_pol_67_);
v_res_69_ = l_Std_Sat_CNF_Clause_add___redArg(v_c_65_, v_atom_66_, v_pol_boxed_68_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add(lean_object* v_00_u03b1_70_, lean_object* v_c_71_, lean_object* v_atom_72_, uint8_t v_pol_73_){
_start:
{
lean_object* v_atoms_74_; lean_object* v_polarities_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_88_; 
v_atoms_74_ = lean_ctor_get(v_c_71_, 0);
v_polarities_75_ = lean_ctor_get(v_c_71_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v_c_71_);
if (v_isSharedCheck_88_ == 0)
{
v___x_77_ = v_c_71_;
v_isShared_78_ = v_isSharedCheck_88_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_polarities_75_);
lean_inc(v_atoms_74_);
lean_dec(v_c_71_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_88_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; uint8_t v___y_81_; 
v___x_79_ = lean_array_push(v_atoms_74_, v_atom_72_);
if (v_pol_73_ == 0)
{
uint8_t v___x_86_; 
v___x_86_ = 0;
v___y_81_ = v___x_86_;
goto v___jp_80_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = 1;
v___y_81_ = v___x_87_;
goto v___jp_80_;
}
v___jp_80_:
{
lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_82_ = lean_byte_array_push(v_polarities_75_, v___y_81_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_82_);
lean_ctor_set(v___x_77_, 0, v___x_79_);
v___x_84_ = v___x_77_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add___boxed(lean_object* v_00_u03b1_89_, lean_object* v_c_90_, lean_object* v_atom_91_, lean_object* v_pol_92_){
_start:
{
uint8_t v_pol_boxed_93_; lean_object* v_res_94_; 
v_pol_boxed_93_ = lean_unbox(v_pol_92_);
v_res_94_ = l_Std_Sat_CNF_Clause_add(v_00_u03b1_89_, v_c_90_, v_atom_91_, v_pol_boxed_93_);
return v_res_94_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_polarity___redArg(lean_object* v_c_95_, lean_object* v_i_96_){
_start:
{
lean_object* v_polarities_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_polarities_97_ = lean_ctor_get(v_c_95_, 1);
v___x_98_ = lean_byte_array_size(v_polarities_97_);
v___x_99_ = lean_nat_dec_lt(v_i_96_, v___x_98_);
if (v___x_99_ == 0)
{
return v___x_99_;
}
else
{
uint8_t v___x_100_; uint8_t v___x_101_; uint8_t v___x_102_; 
v___x_100_ = lean_byte_array_fget(v_polarities_97_, v_i_96_);
v___x_101_ = 1;
v___x_102_ = lean_uint8_dec_eq(v___x_100_, v___x_101_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_polarity___redArg___boxed(lean_object* v_c_103_, lean_object* v_i_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_103_, v_i_104_);
lean_dec(v_i_104_);
lean_dec_ref(v_c_103_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_polarity(lean_object* v_00_u03b1_107_, lean_object* v_c_108_, lean_object* v_i_109_){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_108_, v_i_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_polarity___boxed(lean_object* v_00_u03b1_111_, lean_object* v_c_112_, lean_object* v_i_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Std_Sat_CNF_Clause_polarity(v_00_u03b1_111_, v_c_112_, v_i_113_);
lean_dec(v_i_113_);
lean_dec_ref(v_c_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(lean_object* v_c_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
if (lean_obj_tag(v_a_117_) == 0)
{
lean_object* v___x_119_; 
v___x_119_ = l_List_reverse___redArg(v_a_118_);
return v___x_119_;
}
else
{
lean_object* v_head_120_; lean_object* v_tail_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_140_; 
v_head_120_ = lean_ctor_get(v_a_117_, 0);
v_tail_121_ = lean_ctor_get(v_a_117_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_a_117_);
if (v_isSharedCheck_140_ == 0)
{
v___x_123_ = v_a_117_;
v_isShared_124_ = v_isSharedCheck_140_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_tail_121_);
lean_inc(v_head_120_);
lean_dec(v_a_117_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_140_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_fst_125_; lean_object* v_snd_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_139_; 
v_fst_125_ = lean_ctor_get(v_head_120_, 0);
v_snd_126_ = lean_ctor_get(v_head_120_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_head_120_);
if (v_isSharedCheck_139_ == 0)
{
v___x_128_ = v_head_120_;
v_isShared_129_ = v_isSharedCheck_139_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_snd_126_);
lean_inc(v_fst_125_);
lean_dec(v_head_120_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_139_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_130_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_116_, v_snd_126_);
lean_dec(v_snd_126_);
v___x_131_ = lean_box(v___x_130_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v___x_131_);
v___x_133_ = v___x_128_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_fst_125_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_138_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_135_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v_a_118_);
lean_ctor_set(v___x_123_, 0, v___x_133_);
v___x_135_ = v___x_123_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_a_118_);
v___x_135_ = v_reuseFailAlloc_137_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
v_a_117_ = v_tail_121_;
v_a_118_ = v___x_135_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg___boxed(lean_object* v_c_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(v_c_141_, v_a_142_, v_a_143_);
lean_dec_ref(v_c_141_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_literals___redArg(lean_object* v_c_145_){
_start:
{
lean_object* v_atoms_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_atoms_146_ = lean_ctor_get(v_c_145_, 0);
lean_inc_ref(v_atoms_146_);
v___x_147_ = lean_array_to_list(v_atoms_146_);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = l_List_zipIdx___redArg(v___x_147_, v___x_148_);
v___x_150_ = lean_box(0);
v___x_151_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(v_c_145_, v___x_149_, v___x_150_);
lean_dec_ref(v_c_145_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_literals(lean_object* v_00_u03b1_152_, lean_object* v_c_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_Sat_CNF_Clause_literals___redArg(v_c_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0(lean_object* v_00_u03b1_155_, lean_object* v_c_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(v_c_156_, v_a_157_, v_a_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___boxed(lean_object* v_00_u03b1_160_, lean_object* v_c_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0(v_00_u03b1_160_, v_c_161_, v_a_162_, v_a_163_);
lean_dec_ref(v_c_161_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0___redArg(lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
return v_x_165_;
}
else
{
lean_object* v_head_167_; lean_object* v_tail_168_; lean_object* v_fst_169_; lean_object* v_snd_170_; lean_object* v_atoms_171_; lean_object* v_polarities_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_187_; 
v_head_167_ = lean_ctor_get(v_x_166_, 0);
lean_inc(v_head_167_);
v_tail_168_ = lean_ctor_get(v_x_166_, 1);
lean_inc(v_tail_168_);
lean_dec_ref_known(v_x_166_, 2);
v_fst_169_ = lean_ctor_get(v_head_167_, 0);
lean_inc(v_fst_169_);
v_snd_170_ = lean_ctor_get(v_head_167_, 1);
lean_inc(v_snd_170_);
lean_dec(v_head_167_);
v_atoms_171_ = lean_ctor_get(v_x_165_, 0);
v_polarities_172_ = lean_ctor_get(v_x_165_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_187_ == 0)
{
v___x_174_ = v_x_165_;
v_isShared_175_ = v_isSharedCheck_187_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_polarities_172_);
lean_inc(v_atoms_171_);
lean_dec(v_x_165_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_187_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; uint8_t v___y_178_; uint8_t v___x_184_; 
v___x_176_ = lean_array_push(v_atoms_171_, v_fst_169_);
v___x_184_ = lean_unbox(v_snd_170_);
lean_dec(v_snd_170_);
if (v___x_184_ == 0)
{
uint8_t v___x_185_; 
v___x_185_ = 0;
v___y_178_ = v___x_185_;
goto v___jp_177_;
}
else
{
uint8_t v___x_186_; 
v___x_186_ = 1;
v___y_178_ = v___x_186_;
goto v___jp_177_;
}
v___jp_177_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_byte_array_push(v_polarities_172_, v___y_178_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_179_);
lean_ctor_set(v___x_174_, 0, v___x_176_);
v___x_181_ = v___x_174_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_179_);
v___x_181_ = v_reuseFailAlloc_183_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
v_x_165_ = v___x_181_;
v_x_166_ = v_tail_168_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_ofLiterals___redArg(lean_object* v_l_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___closed__1, &l_Std_Sat_CNF_Clause_empty___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___closed__1);
v___x_190_ = l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0___redArg(v___x_189_, v_l_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_ofLiterals(lean_object* v_00_u03b1_191_, lean_object* v_l_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Std_Sat_CNF_Clause_ofLiterals___redArg(v_l_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0(lean_object* v_00_u03b1_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0___redArg(v_x_195_, v_x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instMembershipLiteral(lean_object* v_00_u03b1_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_box(0);
return v___x_199_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(lean_object* v_inst_200_, lean_object* v_c_201_, lean_object* v_lit_202_, lean_object* v_i_203_){
_start:
{
lean_object* v_atoms_208_; lean_object* v_polarities_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_atoms_208_ = lean_ctor_get(v_c_201_, 0);
v_polarities_209_ = lean_ctor_get(v_c_201_, 1);
v___x_210_ = lean_array_get_size(v_atoms_208_);
v___x_211_ = lean_nat_dec_lt(v_i_203_, v___x_210_);
if (v___x_211_ == 0)
{
lean_dec(v_i_203_);
lean_dec_ref(v_lit_202_);
lean_dec_ref(v_inst_200_);
return v___x_211_;
}
else
{
lean_object* v_fst_212_; lean_object* v_snd_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_fst_212_ = lean_ctor_get(v_lit_202_, 0);
v_snd_213_ = lean_ctor_get(v_lit_202_, 1);
v___x_214_ = lean_array_fget_borrowed(v_atoms_208_, v_i_203_);
lean_inc_ref(v_inst_200_);
lean_inc(v_fst_212_);
lean_inc(v___x_214_);
v___x_215_ = lean_apply_2(v_inst_200_, v___x_214_, v_fst_212_);
v___x_216_ = lean_unbox(v___x_215_);
if (v___x_216_ == 0)
{
goto v___jp_204_;
}
else
{
uint8_t v___x_217_; uint8_t v___x_218_; uint8_t v___x_219_; uint8_t v___x_220_; 
v___x_217_ = lean_byte_array_fget(v_polarities_209_, v_i_203_);
v___x_218_ = 1;
v___x_219_ = lean_uint8_dec_eq(v___x_217_, v___x_218_);
v___x_220_ = lean_unbox(v_snd_213_);
if (v___x_220_ == 0)
{
if (v___x_219_ == 0)
{
lean_dec(v_i_203_);
lean_dec_ref(v_lit_202_);
lean_dec_ref(v_inst_200_);
return v___x_211_;
}
else
{
goto v___jp_204_;
}
}
else
{
if (v___x_219_ == 0)
{
goto v___jp_204_;
}
else
{
lean_dec(v_i_203_);
lean_dec_ref(v_lit_202_);
lean_dec_ref(v_inst_200_);
return v___x_211_;
}
}
}
}
v___jp_204_:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_add(v_i_203_, v___x_205_);
lean_dec(v_i_203_);
v_i_203_ = v___x_206_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg___boxed(lean_object* v_inst_221_, lean_object* v_c_222_, lean_object* v_lit_223_, lean_object* v_i_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_221_, v_c_222_, v_lit_223_, v_i_224_);
lean_dec_ref(v_c_222_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go(lean_object* v_00_u03b1_227_, lean_object* v_inst_228_, lean_object* v_c_229_, lean_object* v_lit_230_, lean_object* v_i_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_228_, v_c_229_, v_lit_230_, v_i_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___boxed(lean_object* v_00_u03b1_233_, lean_object* v_inst_234_, lean_object* v_c_235_, lean_object* v_lit_236_, lean_object* v_i_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go(v_00_u03b1_233_, v_inst_234_, v_c_235_, v_lit_236_, v_i_237_);
lean_dec_ref(v_c_235_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_contains___redArg(lean_object* v_inst_240_, lean_object* v_c_241_, lean_object* v_lit_242_){
_start:
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_240_, v_c_241_, v_lit_242_, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_contains___redArg___boxed(lean_object* v_inst_245_, lean_object* v_c_246_, lean_object* v_lit_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Std_Sat_CNF_Clause_contains___redArg(v_inst_245_, v_c_246_, v_lit_247_);
lean_dec_ref(v_c_246_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_contains(lean_object* v_00_u03b1_250_, lean_object* v_inst_251_, lean_object* v_c_252_, lean_object* v_lit_253_){
_start:
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_251_, v_c_252_, v_lit_253_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_contains___boxed(lean_object* v_00_u03b1_256_, lean_object* v_inst_257_, lean_object* v_c_258_, lean_object* v_lit_259_){
_start:
{
uint8_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l_Std_Sat_CNF_Clause_contains(v_00_u03b1_256_, v_inst_257_, v_c_258_, v_lit_259_);
lean_dec_ref(v_c_258_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(lean_object* v_inst_262_, lean_object* v_lit_263_, lean_object* v_c_264_){
_start:
{
lean_object* v___f_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___f_265_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_265_, 0, v_inst_262_);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v___f_265_, v_c_264_, v_lit_263_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg___boxed(lean_object* v_inst_268_, lean_object* v_lit_269_, lean_object* v_c_270_){
_start:
{
uint8_t v_res_271_; lean_object* v_r_272_; 
v_res_271_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v_inst_268_, v_lit_269_, v_c_270_);
lean_dec_ref(v_c_270_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq(lean_object* v_00_u03b1_273_, lean_object* v_inst_274_, lean_object* v_lit_275_, lean_object* v_c_276_){
_start:
{
uint8_t v___x_277_; 
v___x_277_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v_inst_274_, v_lit_275_, v_c_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___boxed(lean_object* v_00_u03b1_278_, lean_object* v_inst_279_, lean_object* v_lit_280_, lean_object* v_c_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq(v_00_u03b1_278_, v_inst_279_, v_lit_280_, v_c_281_);
lean_dec_ref(v_c_281_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_284_, lean_object* v_i_285_, lean_object* v_inst_286_, lean_object* v_c_287_, lean_object* v_f_288_, lean_object* v_sz_289_, lean_object* v_____do__lift_290_){
_start:
{
size_t v_i_boxed_291_; size_t v_sz_boxed_292_; lean_object* v_res_293_; 
v_i_boxed_291_ = lean_unbox_usize(v_i_285_);
lean_dec(v_i_285_);
v_sz_boxed_292_ = lean_unbox_usize(v_sz_289_);
lean_dec(v_sz_289_);
v_res_293_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0(v_toPure_284_, v_i_boxed_291_, v_inst_286_, v_c_287_, v_f_288_, v_sz_boxed_292_, v_____do__lift_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(lean_object* v_inst_294_, lean_object* v_c_295_, lean_object* v_f_296_, size_t v_sz_297_, size_t v_i_298_, lean_object* v_b_299_){
_start:
{
lean_object* v_toApplicative_300_; lean_object* v_toBind_301_; lean_object* v_toPure_302_; uint8_t v___x_303_; 
v_toApplicative_300_ = lean_ctor_get(v_inst_294_, 0);
v_toBind_301_ = lean_ctor_get(v_inst_294_, 1);
lean_inc(v_toBind_301_);
v_toPure_302_ = lean_ctor_get(v_toApplicative_300_, 1);
lean_inc(v_toPure_302_);
v___x_303_ = lean_usize_dec_lt(v_i_298_, v_sz_297_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
lean_dec(v_toBind_301_);
lean_dec(v_f_296_);
lean_dec_ref(v_c_295_);
lean_dec_ref(v_inst_294_);
v___x_304_ = lean_apply_2(v_toPure_302_, lean_box(0), v_b_299_);
return v___x_304_;
}
else
{
lean_object* v_atoms_305_; lean_object* v_polarities_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___f_309_; lean_object* v___x_310_; uint8_t v___x_311_; uint8_t v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_atoms_305_ = lean_ctor_get(v_c_295_, 0);
lean_inc_ref(v_atoms_305_);
v_polarities_306_ = lean_ctor_get(v_c_295_, 1);
lean_inc_ref(v_polarities_306_);
v___x_307_ = lean_box_usize(v_i_298_);
v___x_308_ = lean_box_usize(v_sz_297_);
lean_inc(v_f_296_);
v___f_309_ = lean_alloc_closure((void*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_309_, 0, v_toPure_302_);
lean_closure_set(v___f_309_, 1, v___x_307_);
lean_closure_set(v___f_309_, 2, v_inst_294_);
lean_closure_set(v___f_309_, 3, v_c_295_);
lean_closure_set(v___f_309_, 4, v_f_296_);
lean_closure_set(v___f_309_, 5, v___x_308_);
v___x_310_ = lean_array_uget(v_atoms_305_, v_i_298_);
lean_dec_ref(v_atoms_305_);
v___x_311_ = lean_byte_array_uget(v_polarities_306_, v_i_298_);
lean_dec_ref(v_polarities_306_);
v___x_312_ = 1;
v___x_313_ = lean_uint8_dec_eq(v___x_311_, v___x_312_);
v___x_314_ = lean_box(v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_310_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_apply_3(v_f_296_, v___x_315_, lean_box(0), v_b_299_);
v___x_317_ = lean_apply_4(v_toBind_301_, lean_box(0), lean_box(0), v___x_316_, v___f_309_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0(lean_object* v_toPure_318_, size_t v_i_319_, lean_object* v_inst_320_, lean_object* v_c_321_, lean_object* v_f_322_, size_t v_sz_323_, lean_object* v_____do__lift_324_){
_start:
{
if (lean_obj_tag(v_____do__lift_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; 
lean_dec(v_f_322_);
lean_dec_ref(v_c_321_);
lean_dec_ref(v_inst_320_);
v_a_325_ = lean_ctor_get(v_____do__lift_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v_____do__lift_324_, 1);
v___x_326_ = lean_apply_2(v_toPure_318_, lean_box(0), v_a_325_);
return v___x_326_;
}
else
{
lean_object* v_a_327_; size_t v___x_328_; size_t v___x_329_; lean_object* v___x_330_; 
lean_dec(v_toPure_318_);
v_a_327_ = lean_ctor_get(v_____do__lift_324_, 0);
lean_inc(v_a_327_);
lean_dec_ref_known(v_____do__lift_324_, 1);
v___x_328_ = ((size_t)1ULL);
v___x_329_ = lean_usize_add(v_i_319_, v___x_328_);
v___x_330_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_320_, v_c_321_, v_f_322_, v_sz_323_, v___x_329_, v_a_327_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___boxed(lean_object* v_inst_331_, lean_object* v_c_332_, lean_object* v_f_333_, lean_object* v_sz_334_, lean_object* v_i_335_, lean_object* v_b_336_){
_start:
{
size_t v_sz_boxed_337_; size_t v_i_boxed_338_; lean_object* v_res_339_; 
v_sz_boxed_337_ = lean_unbox_usize(v_sz_334_);
lean_dec(v_sz_334_);
v_i_boxed_338_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_res_339_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_331_, v_c_332_, v_f_333_, v_sz_boxed_337_, v_i_boxed_338_, v_b_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop(lean_object* v_m_340_, lean_object* v_00_u03b1_341_, lean_object* v_00_u03b2_342_, lean_object* v_inst_343_, lean_object* v_c_344_, lean_object* v_f_345_, size_t v_sz_346_, size_t v_i_347_, lean_object* v_b_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_343_, v_c_344_, v_f_345_, v_sz_346_, v_i_347_, v_b_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___boxed(lean_object* v_m_350_, lean_object* v_00_u03b1_351_, lean_object* v_00_u03b2_352_, lean_object* v_inst_353_, lean_object* v_c_354_, lean_object* v_f_355_, lean_object* v_sz_356_, lean_object* v_i_357_, lean_object* v_b_358_){
_start:
{
size_t v_sz_boxed_359_; size_t v_i_boxed_360_; lean_object* v_res_361_; 
v_sz_boxed_359_ = lean_unbox_usize(v_sz_356_);
lean_dec(v_sz_356_);
v_i_boxed_360_ = lean_unbox_usize(v_i_357_);
lean_dec(v_i_357_);
v_res_361_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop(v_m_350_, v_00_u03b1_351_, v_00_u03b2_352_, v_inst_353_, v_c_354_, v_f_355_, v_sz_boxed_359_, v_i_boxed_360_, v_b_358_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_forIn_x27ImplUnsafe___redArg(lean_object* v_inst_362_, lean_object* v_c_363_, lean_object* v_b_364_, lean_object* v_f_365_){
_start:
{
lean_object* v_atoms_366_; size_t v_sz_367_; size_t v___x_368_; lean_object* v___x_369_; 
v_atoms_366_ = lean_ctor_get(v_c_363_, 0);
v_sz_367_ = lean_array_size(v_atoms_366_);
v___x_368_ = ((size_t)0ULL);
v___x_369_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_362_, v_c_363_, v_f_365_, v_sz_367_, v___x_368_, v_b_364_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_forIn_x27ImplUnsafe(lean_object* v_m_370_, lean_object* v_00_u03b1_371_, lean_object* v_00_u03b2_372_, lean_object* v_inst_373_, lean_object* v_c_374_, lean_object* v_b_375_, lean_object* v_f_376_){
_start:
{
lean_object* v_atoms_377_; size_t v_sz_378_; size_t v___x_379_; lean_object* v___x_380_; 
v_atoms_377_ = lean_ctor_get(v_c_374_, 0);
v_sz_378_ = lean_array_size(v_atoms_377_);
v___x_379_ = ((size_t)0ULL);
v___x_380_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_373_, v_c_374_, v_f_376_, v_sz_378_, v___x_379_, v_b_375_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0___boxed(lean_object* v_toPure_381_, lean_object* v_i_382_, lean_object* v_inst_383_, lean_object* v_c_384_, lean_object* v_f_385_, lean_object* v_____do__lift_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0(v_toPure_381_, v_i_382_, v_inst_383_, v_c_384_, v_f_385_, v_____do__lift_386_);
lean_dec(v_i_382_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg(lean_object* v_inst_388_, lean_object* v_c_389_, lean_object* v_f_390_, lean_object* v_i_391_, lean_object* v_b_392_){
_start:
{
lean_object* v_toApplicative_393_; lean_object* v_atoms_394_; lean_object* v_toBind_395_; lean_object* v_toPure_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_toApplicative_393_ = lean_ctor_get(v_inst_388_, 0);
v_atoms_394_ = lean_ctor_get(v_c_389_, 0);
v_toBind_395_ = lean_ctor_get(v_inst_388_, 1);
lean_inc(v_toBind_395_);
v_toPure_396_ = lean_ctor_get(v_toApplicative_393_, 1);
lean_inc(v_toPure_396_);
v___x_397_ = lean_array_get_size(v_atoms_394_);
v___x_398_ = lean_nat_dec_lt(v_i_391_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec(v_toBind_395_);
lean_dec(v_i_391_);
lean_dec(v_f_390_);
lean_dec_ref(v_c_389_);
lean_dec_ref(v_inst_388_);
v___x_399_ = lean_apply_2(v_toPure_396_, lean_box(0), v_b_392_);
return v___x_399_;
}
else
{
lean_object* v___f_400_; lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_412_; 
lean_inc(v_f_390_);
lean_inc_ref(v_c_389_);
lean_inc(v_i_391_);
v___f_400_ = lean_alloc_closure((void*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_400_, 0, v_toPure_396_);
lean_closure_set(v___f_400_, 1, v_i_391_);
lean_closure_set(v___f_400_, 2, v_inst_388_);
lean_closure_set(v___f_400_, 3, v_c_389_);
lean_closure_set(v___f_400_, 4, v_f_390_);
v___x_401_ = lean_array_fget(v_atoms_394_, v_i_391_);
v___x_402_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_389_, v_i_391_);
lean_dec(v_i_391_);
v_isSharedCheck_412_ = !lean_is_exclusive(v_c_389_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; lean_object* v_unused_414_; 
v_unused_413_ = lean_ctor_get(v_c_389_, 1);
lean_dec(v_unused_413_);
v_unused_414_ = lean_ctor_get(v_c_389_, 0);
lean_dec(v_unused_414_);
v___x_404_ = v_c_389_;
v_isShared_405_ = v_isSharedCheck_412_;
goto v_resetjp_403_;
}
else
{
lean_dec(v_c_389_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_412_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_box(v___x_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_406_);
lean_ctor_set(v___x_404_, 0, v___x_401_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_406_);
v___x_408_ = v_reuseFailAlloc_411_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_apply_3(v_f_390_, v___x_408_, lean_box(0), v_b_392_);
v___x_410_ = lean_apply_4(v_toBind_395_, lean_box(0), lean_box(0), v___x_409_, v___f_400_);
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0(lean_object* v_toPure_415_, lean_object* v_i_416_, lean_object* v_inst_417_, lean_object* v_c_418_, lean_object* v_f_419_, lean_object* v_____do__lift_420_){
_start:
{
if (lean_obj_tag(v_____do__lift_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_422_; 
lean_dec(v_f_419_);
lean_dec_ref(v_c_418_);
lean_dec_ref(v_inst_417_);
v_a_421_ = lean_ctor_get(v_____do__lift_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v_____do__lift_420_, 1);
v___x_422_ = lean_apply_2(v_toPure_415_, lean_box(0), v_a_421_);
return v___x_422_;
}
else
{
lean_object* v_a_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v_toPure_415_);
v_a_423_ = lean_ctor_get(v_____do__lift_420_, 0);
lean_inc(v_a_423_);
lean_dec_ref_known(v_____do__lift_420_, 1);
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_nat_add(v_i_416_, v___x_424_);
v___x_426_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg(v_inst_417_, v_c_418_, v_f_419_, v___x_425_, v_a_423_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go(lean_object* v_m_427_, lean_object* v_00_u03b1_428_, lean_object* v_00_u03b2_429_, lean_object* v_inst_430_, lean_object* v_c_431_, lean_object* v_f_432_, lean_object* v_i_433_, lean_object* v_b_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg(v_inst_430_, v_c_431_, v_f_432_, v_i_433_, v_b_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop_match__1_splitter___redArg(lean_object* v_____do__lift_436_, lean_object* v_h__1_437_, lean_object* v_h__2_438_){
_start:
{
if (lean_obj_tag(v_____do__lift_436_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
lean_dec(v_h__2_438_);
v_a_439_ = lean_ctor_get(v_____do__lift_436_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v_____do__lift_436_, 1);
v___x_440_ = lean_apply_1(v_h__1_437_, v_a_439_);
return v___x_440_;
}
else
{
lean_object* v_a_441_; lean_object* v___x_442_; 
lean_dec(v_h__1_437_);
v_a_441_ = lean_ctor_get(v_____do__lift_436_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v_____do__lift_436_, 1);
v___x_442_ = lean_apply_1(v_h__2_438_, v_a_441_);
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop_match__1_splitter(lean_object* v_00_u03b2_443_, lean_object* v_motive_444_, lean_object* v_____do__lift_445_, lean_object* v_h__1_446_, lean_object* v_h__2_447_){
_start:
{
if (lean_obj_tag(v_____do__lift_445_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; 
lean_dec(v_h__2_447_);
v_a_448_ = lean_ctor_get(v_____do__lift_445_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v_____do__lift_445_, 1);
v___x_449_ = lean_apply_1(v_h__1_446_, v_a_448_);
return v___x_449_;
}
else
{
lean_object* v_a_450_; lean_object* v___x_451_; 
lean_dec(v_h__1_446_);
v_a_450_ = lean_ctor_get(v_____do__lift_445_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v_____do__lift_445_, 1);
v___x_451_ = lean_apply_1(v_h__2_447_, v_a_450_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_452_, lean_object* v_00_u03b2_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_atoms_457_; size_t v_sz_458_; size_t v___x_459_; lean_object* v___x_460_; 
v_atoms_457_ = lean_ctor_get(v___y_454_, 0);
v_sz_458_ = lean_array_size(v_atoms_457_);
v___x_459_ = ((size_t)0ULL);
v___x_460_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_452_, v___y_454_, v___y_456_, v_sz_458_, v___x_459_, v___y_455_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg(lean_object* v_inst_461_){
_start:
{
lean_object* v___f_462_; 
v___f_462_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_462_, 0, v_inst_461_);
return v___f_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad(lean_object* v_m_463_, lean_object* v_00_u03b1_464_, lean_object* v_inst_465_){
_start:
{
lean_object* v___f_466_; 
v___f_466_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_466_, 0, v_inst_465_);
return v___f_466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_467_, lean_object* v_h__1_468_, lean_object* v_h__2_469_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; 
lean_dec(v_h__2_469_);
v_a_470_ = lean_ctor_get(v_x_467_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v_x_467_, 1);
v___x_471_ = lean_apply_1(v_h__1_468_, v_a_470_);
return v___x_471_;
}
else
{
lean_object* v_a_472_; lean_object* v___x_473_; 
lean_dec(v_h__1_468_);
v_a_472_ = lean_ctor_get(v_x_467_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v_x_467_, 1);
v___x_473_ = lean_apply_1(v_h__2_469_, v_a_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_474_, lean_object* v_motive_475_, lean_object* v_x_476_, lean_object* v_h__1_477_, lean_object* v_h__2_478_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
lean_dec(v_h__2_478_);
v_a_479_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v_x_476_, 1);
v___x_480_ = lean_apply_1(v_h__1_477_, v_a_479_);
return v___x_480_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_482_; 
lean_dec(v_h__1_477_);
v_a_481_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v_x_476_, 1);
v___x_482_ = lean_apply_1(v_h__2_478_, v_a_481_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(lean_object* v_inst_483_, lean_object* v_c_484_, lean_object* v_lit_485_, lean_object* v_i_486_, lean_object* v_acc_487_){
_start:
{
lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; uint8_t v___y_492_; lean_object* v_atoms_496_; lean_object* v_polarities_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_atoms_496_ = lean_ctor_get(v_c_484_, 0);
v_polarities_497_ = lean_ctor_get(v_c_484_, 1);
v___x_498_ = lean_array_get_size(v_atoms_496_);
v___x_499_ = lean_nat_dec_lt(v_i_486_, v___x_498_);
if (v___x_499_ == 0)
{
lean_dec(v_i_486_);
lean_dec_ref(v_lit_485_);
lean_dec_ref(v_inst_483_);
return v_acc_487_;
}
else
{
lean_object* v_fst_500_; lean_object* v_snd_501_; lean_object* v_atom_502_; uint8_t v___x_503_; lean_object* v___x_504_; uint8_t v___x_508_; uint8_t v_pol_509_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_fst_500_ = lean_ctor_get(v_lit_485_, 0);
v_snd_501_ = lean_ctor_get(v_lit_485_, 1);
v_atom_502_ = lean_array_fget_borrowed(v_atoms_496_, v_i_486_);
v___x_503_ = lean_byte_array_fget(v_polarities_497_, v_i_486_);
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_508_ = 1;
v_pol_509_ = lean_uint8_dec_eq(v___x_503_, v___x_508_);
lean_inc_ref(v_inst_483_);
lean_inc(v_fst_500_);
lean_inc(v_atom_502_);
v___x_516_ = lean_apply_2(v_inst_483_, v_atom_502_, v_fst_500_);
v___x_517_ = lean_unbox(v___x_516_);
if (v___x_517_ == 0)
{
goto v___jp_510_;
}
else
{
uint8_t v___x_518_; 
v___x_518_ = lean_unbox(v_snd_501_);
if (v___x_518_ == 0)
{
if (v_pol_509_ == 0)
{
goto v___jp_505_;
}
else
{
goto v___jp_510_;
}
}
else
{
if (v_pol_509_ == 0)
{
goto v___jp_510_;
}
else
{
goto v___jp_505_;
}
}
}
v___jp_505_:
{
lean_object* v___x_506_; 
v___x_506_ = lean_nat_add(v_i_486_, v___x_504_);
lean_dec(v_i_486_);
v_i_486_ = v___x_506_;
goto _start;
}
v___jp_510_:
{
lean_object* v_atoms_511_; lean_object* v_polarities_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_atoms_511_ = lean_ctor_get(v_acc_487_, 0);
lean_inc_ref(v_atoms_511_);
v_polarities_512_ = lean_ctor_get(v_acc_487_, 1);
lean_inc_ref(v_polarities_512_);
lean_dec_ref(v_acc_487_);
v___x_513_ = lean_nat_add(v_i_486_, v___x_504_);
lean_dec(v_i_486_);
lean_inc(v_atom_502_);
v___x_514_ = lean_array_push(v_atoms_511_, v_atom_502_);
if (v_pol_509_ == 0)
{
uint8_t v___x_515_; 
v___x_515_ = 0;
v___y_489_ = v___x_514_;
v___y_490_ = v___x_513_;
v___y_491_ = v_polarities_512_;
v___y_492_ = v___x_515_;
goto v___jp_488_;
}
else
{
v___y_489_ = v___x_514_;
v___y_490_ = v___x_513_;
v___y_491_ = v_polarities_512_;
v___y_492_ = v___x_508_;
goto v___jp_488_;
}
}
}
v___jp_488_:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_byte_array_push(v___y_491_, v___y_492_);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___y_489_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v_i_486_ = v___y_490_;
v_acc_487_ = v___x_494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg___boxed(lean_object* v_inst_519_, lean_object* v_c_520_, lean_object* v_lit_521_, lean_object* v_i_522_, lean_object* v_acc_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(v_inst_519_, v_c_520_, v_lit_521_, v_i_522_, v_acc_523_);
lean_dec_ref(v_c_520_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go(lean_object* v_00_u03b1_525_, lean_object* v_inst_526_, lean_object* v_c_527_, lean_object* v_lit_528_, lean_object* v_i_529_, lean_object* v_acc_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(v_inst_526_, v_c_527_, v_lit_528_, v_i_529_, v_acc_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___boxed(lean_object* v_00_u03b1_532_, lean_object* v_inst_533_, lean_object* v_c_534_, lean_object* v_lit_535_, lean_object* v_i_536_, lean_object* v_acc_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go(v_00_u03b1_532_, v_inst_533_, v_c_534_, v_lit_535_, v_i_536_, v_acc_537_);
lean_dec_ref(v_c_534_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase___redArg(lean_object* v_inst_539_, lean_object* v_c_540_, lean_object* v_lit_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___closed__1, &l_Std_Sat_CNF_Clause_empty___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___closed__1);
v___x_544_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(v_inst_539_, v_c_540_, v_lit_541_, v___x_542_, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase___redArg___boxed(lean_object* v_inst_545_, lean_object* v_c_546_, lean_object* v_lit_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Sat_CNF_Clause_erase___redArg(v_inst_545_, v_c_546_, v_lit_547_);
lean_dec_ref(v_c_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase(lean_object* v_00_u03b1_549_, lean_object* v_inst_550_, lean_object* v_c_551_, lean_object* v_lit_552_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___closed__1, &l_Std_Sat_CNF_Clause_empty___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___closed__1);
v___x_555_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(v_inst_550_, v_c_551_, v_lit_552_, v___x_553_, v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase___boxed(lean_object* v_00_u03b1_556_, lean_object* v_inst_557_, lean_object* v_c_558_, lean_object* v_lit_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_Sat_CNF_Clause_erase(v_00_u03b1_556_, v_inst_557_, v_c_558_, v_lit_559_);
lean_dec_ref(v_c_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_append___redArg(lean_object* v_c1_561_, lean_object* v_c2_562_){
_start:
{
lean_object* v_atoms_563_; lean_object* v_polarities_564_; lean_object* v_atoms_565_; lean_object* v_polarities_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_579_; 
v_atoms_563_ = lean_ctor_get(v_c1_561_, 0);
lean_inc_ref(v_atoms_563_);
v_polarities_564_ = lean_ctor_get(v_c1_561_, 1);
lean_inc_ref(v_polarities_564_);
lean_dec_ref(v_c1_561_);
v_atoms_565_ = lean_ctor_get(v_c2_562_, 0);
v_polarities_566_ = lean_ctor_get(v_c2_562_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_c2_562_);
if (v_isSharedCheck_579_ == 0)
{
v___x_568_ = v_c2_562_;
v_isShared_569_ = v_isSharedCheck_579_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_polarities_566_);
lean_inc(v_atoms_565_);
lean_dec(v_c2_562_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_579_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_570_ = l_Array_append___redArg(v_atoms_563_, v_atoms_565_);
lean_dec_ref(v_atoms_565_);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = lean_byte_array_size(v_polarities_564_);
v___x_573_ = lean_byte_array_size(v_polarities_566_);
v___x_574_ = 0;
v___x_575_ = lean_byte_array_copy_slice(v_polarities_566_, v___x_571_, v_polarities_564_, v___x_572_, v___x_573_, v___x_574_);
lean_dec_ref(v_polarities_566_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 1, v___x_575_);
lean_ctor_set(v___x_568_, 0, v___x_570_);
v___x_577_ = v___x_568_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_append(lean_object* v_00_u03b1_580_, lean_object* v_c1_581_, lean_object* v_c2_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_Sat_CNF_Clause_append___redArg(v_c1_581_, v_c2_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instAppend(lean_object* v_00_u03b1_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = ((lean_object*)(l_Std_Sat_CNF_Clause_instAppend___closed__0));
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty(lean_object* v_00_u03b1_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = ((lean_object*)(l_Std_Sat_CNF_empty___closed__0));
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg(lean_object* v_n_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = lean_mk_empty_array_with_capacity(v_n_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg___boxed(lean_object* v_n_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Std_Sat_CNF_emptyWithCapacity___redArg(v_n_593_);
lean_dec(v_n_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity(lean_object* v_00_u03b1_595_, lean_object* v_n_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = lean_mk_empty_array_with_capacity(v_n_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___boxed(lean_object* v_00_u03b1_598_, lean_object* v_n_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_Sat_CNF_emptyWithCapacity(v_00_u03b1_598_, v_n_599_);
lean_dec(v_n_599_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add___redArg(lean_object* v_f_601_, lean_object* v_c_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_array_push(v_f_601_, v_c_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add(lean_object* v_00_u03b1_604_, lean_object* v_f_605_, lean_object* v_c_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = lean_array_push(v_f_605_, v_c_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg(lean_object* v_f1_608_, lean_object* v_f2_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Array_append___redArg(v_f1_608_, v_f2_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg___boxed(lean_object* v_f1_611_, lean_object* v_f2_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_Sat_CNF_append___redArg(v_f1_611_, v_f2_612_);
lean_dec_ref(v_f2_612_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append(lean_object* v_00_u03b1_614_, lean_object* v_f1_615_, lean_object* v_f2_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Array_append___redArg(v_f1_615_, v_f2_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___boxed(lean_object* v_00_u03b1_618_, lean_object* v_f1_619_, lean_object* v_f2_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_Sat_CNF_append(v_00_u03b1_618_, v_f1_619_, v_f2_620_);
lean_dec_ref(v_f2_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend(lean_object* v_00_u03b1_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = ((lean_object*)(l_Std_Sat_CNF_instAppend___closed__0));
return v___x_624_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg(lean_object* v_v_625_, lean_object* v_c_626_, lean_object* v_inst_627_){
_start:
{
lean_object* v_atoms_628_; lean_object* v___f_629_; uint8_t v___x_630_; 
v_atoms_628_ = lean_ctor_get(v_c_626_, 0);
lean_inc_ref(v_atoms_628_);
lean_dec_ref(v_c_626_);
v___f_629_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_629_, 0, v_inst_627_);
v___x_630_ = l_Array_contains___redArg(v___f_629_, v_atoms_628_, v_v_625_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object* v_v_631_, lean_object* v_c_632_, lean_object* v_inst_633_){
_start:
{
uint8_t v_res_634_; lean_object* v_r_635_; 
v_res_634_ = l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg(v_v_631_, v_c_632_, v_inst_633_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq(lean_object* v_00_u03b1_636_, lean_object* v_v_637_, lean_object* v_c_638_, lean_object* v_inst_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg(v_v_637_, v_c_638_, v_inst_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_641_, lean_object* v_v_642_, lean_object* v_c_643_, lean_object* v_inst_644_){
_start:
{
uint8_t v_res_645_; lean_object* v_r_646_; 
v_res_645_ = l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq(v_00_u03b1_641_, v_v_642_, v_c_643_, v_inst_644_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause(lean_object* v_00_u03b1_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = lean_box(0);
return v___x_648_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0(lean_object* v_inst_649_, lean_object* v_a_650_, lean_object* v_b_651_){
_start:
{
uint8_t v___x_652_; 
v___x_652_ = l_Std_Sat_CNF_Clause_instDecidableEq___redArg(v_inst_649_, v_a_650_, v_b_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0___boxed(lean_object* v_inst_653_, lean_object* v_a_654_, lean_object* v_b_655_){
_start:
{
uint8_t v_res_656_; lean_object* v_r_657_; 
v_res_656_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0(v_inst_653_, v_a_654_, v_b_655_);
lean_dec_ref(v_b_655_);
lean_dec_ref(v_a_654_);
v_r_657_ = lean_box(v_res_656_);
return v_r_657_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(lean_object* v_c_658_, lean_object* v_f_659_, lean_object* v_inst_660_){
_start:
{
lean_object* v___f_661_; lean_object* v___f_662_; uint8_t v___x_663_; 
v___f_661_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_661_, 0, v_inst_660_);
v___f_662_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_662_, 0, v___f_661_);
v___x_663_ = l_Array_contains___redArg(v___f_662_, v_f_659_, v_c_658_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___boxed(lean_object* v_c_664_, lean_object* v_f_665_, lean_object* v_inst_666_){
_start:
{
uint8_t v_res_667_; lean_object* v_r_668_; 
v_res_667_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(v_c_664_, v_f_665_, v_inst_666_);
v_r_668_ = lean_box(v_res_667_);
return v_r_668_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(lean_object* v_00_u03b1_669_, lean_object* v_c_670_, lean_object* v_f_671_, lean_object* v_inst_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(v_c_670_, v_f_671_, v_inst_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___boxed(lean_object* v_00_u03b1_674_, lean_object* v_c_675_, lean_object* v_f_676_, lean_object* v_inst_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(v_00_u03b1_674_, v_c_675_, v_f_676_, v_inst_677_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0(lean_object* v_f_680_, lean_object* v_inst_681_, lean_object* v_v_682_, lean_object* v_i_683_, lean_object* v_h_684_){
_start:
{
lean_object* v___x_685_; lean_object* v_atoms_686_; lean_object* v___f_687_; uint8_t v___x_688_; 
v___x_685_ = lean_array_fget_borrowed(v_f_680_, v_i_683_);
v_atoms_686_ = lean_ctor_get(v___x_685_, 0);
v___f_687_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_687_, 0, v_inst_681_);
lean_inc_ref(v_atoms_686_);
v___x_688_ = l_Array_contains___redArg(v___f_687_, v_atoms_686_, v_v_682_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object* v_f_689_, lean_object* v_inst_690_, lean_object* v_v_691_, lean_object* v_i_692_, lean_object* v_h_693_){
_start:
{
uint8_t v_res_694_; lean_object* v_r_695_; 
v_res_694_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0(v_f_689_, v_inst_690_, v_v_691_, v_i_692_, v_h_693_);
lean_dec(v_i_692_);
lean_dec_ref(v_f_689_);
v_r_695_ = lean_box(v_res_694_);
return v_r_695_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(lean_object* v_v_696_, lean_object* v_f_697_, lean_object* v_inst_698_){
_start:
{
lean_object* v___f_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
lean_inc_ref(v_f_697_);
v___f_699_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_699_, 0, v_f_697_);
lean_closure_set(v___f_699_, 1, v_inst_698_);
lean_closure_set(v___f_699_, 2, v_v_696_);
v___x_700_ = lean_array_get_size(v_f_697_);
lean_dec_ref(v_f_697_);
v___x_701_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(v___x_700_, v___f_699_, v___x_700_, lean_box(0));
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object* v_v_702_, lean_object* v_f_703_, lean_object* v_inst_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(v_v_702_, v_f_703_, v_inst_704_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(lean_object* v_00_u03b1_707_, lean_object* v_v_708_, lean_object* v_f_709_, lean_object* v_inst_710_){
_start:
{
uint8_t v___x_711_; 
v___x_711_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(v_v_708_, v_f_709_, v_inst_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_712_, lean_object* v_v_713_, lean_object* v_f_714_, lean_object* v_inst_715_){
_start:
{
uint8_t v_res_716_; lean_object* v_r_717_; 
v_res_716_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(v_00_u03b1_712_, v_v_713_, v_f_714_, v_inst_715_);
v_r_717_ = lean_box(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(uint8_t v___x_718_, lean_object* v_x_719_){
_start:
{
lean_object* v_atoms_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_atoms_720_ = lean_ctor_get(v_x_719_, 0);
v___x_721_ = lean_array_get_size(v_atoms_720_);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_nat_dec_eq(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
return v___x_718_;
}
else
{
uint8_t v___x_724_; 
v___x_724_ = 0;
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object* v___x_725_, lean_object* v_x_726_){
_start:
{
uint8_t v___x_95__boxed_727_; uint8_t v_res_728_; lean_object* v_r_729_; 
v___x_95__boxed_727_ = lean_unbox(v___x_725_);
v_res_728_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(v___x_95__boxed_727_, v_x_726_);
lean_dec_ref(v_x_726_);
v_r_729_ = lean_box(v_res_728_);
return v_r_729_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(lean_object* v_f_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = lean_array_get_size(v_f_749_);
v___x_752_ = ((lean_object*)(l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9));
v___x_753_ = lean_nat_dec_lt(v___x_750_, v___x_751_);
if (v___x_753_ == 0)
{
lean_dec_ref(v_f_749_);
return v___x_753_;
}
else
{
if (v___x_753_ == 0)
{
lean_dec_ref(v_f_749_);
return v___x_753_;
}
else
{
lean_object* v___x_754_; lean_object* v___f_755_; size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_754_ = lean_box(v___x_753_);
v___f_755_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_755_, 0, v___x_754_);
v___x_756_ = ((size_t)0ULL);
v___x_757_ = lean_usize_of_nat(v___x_751_);
v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_752_, v___f_755_, v_f_749_, v___x_756_, v___x_757_);
v___x_759_ = lean_unbox(v___x_758_);
lean_dec(v___x_758_);
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___boxed(lean_object* v_f_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_760_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(lean_object* v_00_u03b1_763_, lean_object* v_f_764_, lean_object* v_inst_765_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_764_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_767_, lean_object* v_f_768_, lean_object* v_inst_769_){
_start:
{
uint8_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(v_00_u03b1_767_, v_f_768_, v_inst_769_);
lean_dec_ref(v_inst_769_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF_Literal(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sat_CNF_Literal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_CNF_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF_Literal(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Literal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_CNF_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
