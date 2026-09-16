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
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Sat_CNF_Clause_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_CNF_Clause_empty___redArg___closed__0 = (const lean_object*)&l_Std_Sat_CNF_Clause_empty___redArg___closed__0_value;
static lean_once_cell_t l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_CNF_Clause_empty___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Sat_CNF_Clause_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_CNF_Clause_instInhabited___closed__0;
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
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instMembershipLiteral___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instMembershipLiteral___redArg___boxed(lean_object*);
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
static const lean_closure_object l_Std_Sat_CNF_Clause_instAppend___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Sat_CNF_Clause_append, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Sat_CNF_Clause_instAppend___redArg___closed__0 = (const lean_object*)&l_Std_Sat_CNF_Clause_instAppend___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instAppend___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instAppend___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instAppend(lean_object*);
static const lean_array_object l_Std_Sat_CNF_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_CNF_empty___redArg___closed__0 = (const lean_object*)&l_Std_Sat_CNF_empty___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty___redArg___boxed(lean_object*);
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
static const lean_closure_object l_Std_Sat_CNF_instAppend___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Sat_CNF_append___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Sat_CNF_instAppend___redArg___closed__0 = (const lean_object*)&l_Std_Sat_CNF_instAppend___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause___redArg___boxed(lean_object*);
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
static lean_object* _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = l_ByteArray_empty;
v___x_29_ = ((lean_object*)(l_Std_Sat_CNF_Clause_empty___redArg___closed__0));
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_empty___redArg(){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___redArg___closed__1, &l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_empty___redArg___boxed(lean_object* v___dummy_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_Sat_CNF_Clause_empty___redArg();
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_empty(lean_object* v_00_u03b1_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___redArg___closed__1, &l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instInhabited___redArg(){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___redArg___closed__1, &l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instInhabited___redArg___boxed(lean_object* v___dummy_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Sat_CNF_Clause_instInhabited___redArg();
return v_res_40_;
}
}
static lean_object* _init_l_Std_Sat_CNF_Clause_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Std_Sat_CNF_Clause_instInhabited___redArg();
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instInhabited(lean_object* v_00_u03b1_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&l_Std_Sat_CNF_Clause_instInhabited___closed__0, &l_Std_Sat_CNF_Clause_instInhabited___closed__0_once, _init_l_Std_Sat_CNF_Clause_instInhabited___closed__0);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size___redArg(lean_object* v_c_44_){
_start:
{
lean_object* v_atoms_45_; lean_object* v___x_46_; 
v_atoms_45_ = lean_ctor_get(v_c_44_, 0);
v___x_46_ = lean_array_get_size(v_atoms_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size___redArg___boxed(lean_object* v_c_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_Sat_CNF_Clause_size___redArg(v_c_47_);
lean_dec_ref(v_c_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size(lean_object* v_00_u03b1_49_, lean_object* v_c_50_){
_start:
{
lean_object* v_atoms_51_; lean_object* v___x_52_; 
v_atoms_51_ = lean_ctor_get(v_c_50_, 0);
v___x_52_ = lean_array_get_size(v_atoms_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size___boxed(lean_object* v_00_u03b1_53_, lean_object* v_c_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_Sat_CNF_Clause_size(v_00_u03b1_53_, v_c_54_);
lean_dec_ref(v_c_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add___redArg(lean_object* v_c_56_, lean_object* v_atom_57_, uint8_t v_pol_58_){
_start:
{
lean_object* v_atoms_59_; lean_object* v_polarities_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_73_; 
v_atoms_59_ = lean_ctor_get(v_c_56_, 0);
v_polarities_60_ = lean_ctor_get(v_c_56_, 1);
v_isSharedCheck_73_ = !lean_is_exclusive(v_c_56_);
if (v_isSharedCheck_73_ == 0)
{
v___x_62_ = v_c_56_;
v_isShared_63_ = v_isSharedCheck_73_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_polarities_60_);
lean_inc(v_atoms_59_);
lean_dec(v_c_56_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_73_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; uint8_t v___y_66_; 
v___x_64_ = lean_array_push(v_atoms_59_, v_atom_57_);
if (v_pol_58_ == 0)
{
uint8_t v___x_71_; 
v___x_71_ = 0;
v___y_66_ = v___x_71_;
goto v___jp_65_;
}
else
{
uint8_t v___x_72_; 
v___x_72_ = 1;
v___y_66_ = v___x_72_;
goto v___jp_65_;
}
v___jp_65_:
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = lean_byte_array_push(v_polarities_60_, v___y_66_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___x_67_);
lean_ctor_set(v___x_62_, 0, v___x_64_);
v___x_69_ = v___x_62_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add___redArg___boxed(lean_object* v_c_74_, lean_object* v_atom_75_, lean_object* v_pol_76_){
_start:
{
uint8_t v_pol_boxed_77_; lean_object* v_res_78_; 
v_pol_boxed_77_ = lean_unbox(v_pol_76_);
v_res_78_ = l_Std_Sat_CNF_Clause_add___redArg(v_c_74_, v_atom_75_, v_pol_boxed_77_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add(lean_object* v_00_u03b1_79_, lean_object* v_c_80_, lean_object* v_atom_81_, uint8_t v_pol_82_){
_start:
{
lean_object* v_atoms_83_; lean_object* v_polarities_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_97_; 
v_atoms_83_ = lean_ctor_get(v_c_80_, 0);
v_polarities_84_ = lean_ctor_get(v_c_80_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v_c_80_);
if (v_isSharedCheck_97_ == 0)
{
v___x_86_ = v_c_80_;
v_isShared_87_ = v_isSharedCheck_97_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_polarities_84_);
lean_inc(v_atoms_83_);
lean_dec(v_c_80_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_97_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; uint8_t v___y_90_; 
v___x_88_ = lean_array_push(v_atoms_83_, v_atom_81_);
if (v_pol_82_ == 0)
{
uint8_t v___x_95_; 
v___x_95_ = 0;
v___y_90_ = v___x_95_;
goto v___jp_89_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 1;
v___y_90_ = v___x_96_;
goto v___jp_89_;
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_byte_array_push(v_polarities_84_, v___y_90_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v___x_91_);
lean_ctor_set(v___x_86_, 0, v___x_88_);
v___x_93_ = v___x_86_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add___boxed(lean_object* v_00_u03b1_98_, lean_object* v_c_99_, lean_object* v_atom_100_, lean_object* v_pol_101_){
_start:
{
uint8_t v_pol_boxed_102_; lean_object* v_res_103_; 
v_pol_boxed_102_ = lean_unbox(v_pol_101_);
v_res_103_ = l_Std_Sat_CNF_Clause_add(v_00_u03b1_98_, v_c_99_, v_atom_100_, v_pol_boxed_102_);
return v_res_103_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_polarity___redArg(lean_object* v_c_104_, lean_object* v_i_105_){
_start:
{
lean_object* v_polarities_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_polarities_106_ = lean_ctor_get(v_c_104_, 1);
v___x_107_ = lean_byte_array_size(v_polarities_106_);
v___x_108_ = lean_nat_dec_lt(v_i_105_, v___x_107_);
if (v___x_108_ == 0)
{
return v___x_108_;
}
else
{
uint8_t v___x_109_; uint8_t v___x_110_; uint8_t v___x_111_; 
v___x_109_ = lean_byte_array_fget(v_polarities_106_, v_i_105_);
v___x_110_ = 1;
v___x_111_ = lean_uint8_dec_eq(v___x_109_, v___x_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_polarity___redArg___boxed(lean_object* v_c_112_, lean_object* v_i_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_112_, v_i_113_);
lean_dec(v_i_113_);
lean_dec_ref(v_c_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_polarity(lean_object* v_00_u03b1_116_, lean_object* v_c_117_, lean_object* v_i_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_117_, v_i_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_polarity___boxed(lean_object* v_00_u03b1_120_, lean_object* v_c_121_, lean_object* v_i_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Std_Sat_CNF_Clause_polarity(v_00_u03b1_120_, v_c_121_, v_i_122_);
lean_dec(v_i_122_);
lean_dec_ref(v_c_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(lean_object* v_c_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
if (lean_obj_tag(v_a_126_) == 0)
{
lean_object* v___x_128_; 
v___x_128_ = l_List_reverse___redArg(v_a_127_);
return v___x_128_;
}
else
{
lean_object* v_head_129_; lean_object* v_tail_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_149_; 
v_head_129_ = lean_ctor_get(v_a_126_, 0);
v_tail_130_ = lean_ctor_get(v_a_126_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_a_126_);
if (v_isSharedCheck_149_ == 0)
{
v___x_132_ = v_a_126_;
v_isShared_133_ = v_isSharedCheck_149_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_tail_130_);
lean_inc(v_head_129_);
lean_dec(v_a_126_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_149_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_fst_134_; lean_object* v_snd_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_148_; 
v_fst_134_ = lean_ctor_get(v_head_129_, 0);
v_snd_135_ = lean_ctor_get(v_head_129_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v_head_129_);
if (v_isSharedCheck_148_ == 0)
{
v___x_137_ = v_head_129_;
v_isShared_138_ = v_isSharedCheck_148_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_snd_135_);
lean_inc(v_fst_134_);
lean_dec(v_head_129_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_148_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_139_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_125_, v_snd_135_);
lean_dec(v_snd_135_);
v___x_140_ = lean_box(v___x_139_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v___x_140_);
v___x_142_ = v___x_137_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_fst_134_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_147_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_a_127_);
lean_ctor_set(v___x_132_, 0, v___x_142_);
v___x_144_ = v___x_132_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_a_127_);
v___x_144_ = v_reuseFailAlloc_146_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
v_a_126_ = v_tail_130_;
v_a_127_ = v___x_144_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg___boxed(lean_object* v_c_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(v_c_150_, v_a_151_, v_a_152_);
lean_dec_ref(v_c_150_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_literals___redArg(lean_object* v_c_154_){
_start:
{
lean_object* v_atoms_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_atoms_155_ = lean_ctor_get(v_c_154_, 0);
lean_inc_ref(v_atoms_155_);
v___x_156_ = lean_array_to_list(v_atoms_155_);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = l_List_zipIdx___redArg(v___x_156_, v___x_157_);
v___x_159_ = lean_box(0);
v___x_160_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(v_c_154_, v___x_158_, v___x_159_);
lean_dec_ref(v_c_154_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_literals(lean_object* v_00_u03b1_161_, lean_object* v_c_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_Sat_CNF_Clause_literals___redArg(v_c_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0(lean_object* v_00_u03b1_164_, lean_object* v_c_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(v_c_165_, v_a_166_, v_a_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___boxed(lean_object* v_00_u03b1_169_, lean_object* v_c_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0(v_00_u03b1_169_, v_c_170_, v_a_171_, v_a_172_);
lean_dec_ref(v_c_170_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0___redArg(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
return v_x_174_;
}
else
{
lean_object* v_head_176_; lean_object* v_tail_177_; lean_object* v_fst_178_; lean_object* v_snd_179_; lean_object* v_atoms_180_; lean_object* v_polarities_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_196_; 
v_head_176_ = lean_ctor_get(v_x_175_, 0);
lean_inc(v_head_176_);
v_tail_177_ = lean_ctor_get(v_x_175_, 1);
lean_inc(v_tail_177_);
lean_dec_ref_known(v_x_175_, 2);
v_fst_178_ = lean_ctor_get(v_head_176_, 0);
lean_inc(v_fst_178_);
v_snd_179_ = lean_ctor_get(v_head_176_, 1);
lean_inc(v_snd_179_);
lean_dec(v_head_176_);
v_atoms_180_ = lean_ctor_get(v_x_174_, 0);
v_polarities_181_ = lean_ctor_get(v_x_174_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_174_);
if (v_isSharedCheck_196_ == 0)
{
v___x_183_ = v_x_174_;
v_isShared_184_ = v_isSharedCheck_196_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_polarities_181_);
lean_inc(v_atoms_180_);
lean_dec(v_x_174_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_196_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; uint8_t v___y_187_; uint8_t v___x_193_; 
v___x_185_ = lean_array_push(v_atoms_180_, v_fst_178_);
v___x_193_ = lean_unbox(v_snd_179_);
lean_dec(v_snd_179_);
if (v___x_193_ == 0)
{
uint8_t v___x_194_; 
v___x_194_ = 0;
v___y_187_ = v___x_194_;
goto v___jp_186_;
}
else
{
uint8_t v___x_195_; 
v___x_195_ = 1;
v___y_187_ = v___x_195_;
goto v___jp_186_;
}
v___jp_186_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = lean_byte_array_push(v_polarities_181_, v___y_187_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___x_188_);
lean_ctor_set(v___x_183_, 0, v___x_185_);
v___x_190_ = v___x_183_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_188_);
v___x_190_ = v_reuseFailAlloc_192_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
v_x_174_ = v___x_190_;
v_x_175_ = v_tail_177_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_ofLiterals___redArg(lean_object* v_l_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___redArg___closed__1, &l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1);
v___x_199_ = l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0___redArg(v___x_198_, v_l_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_ofLiterals(lean_object* v_00_u03b1_200_, lean_object* v_l_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_Sat_CNF_Clause_ofLiterals___redArg(v_l_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0(lean_object* v_00_u03b1_203_, lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0___redArg(v_x_204_, v_x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instMembershipLiteral___redArg(){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_box(0);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instMembershipLiteral___redArg___boxed(lean_object* v___dummy_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Sat_CNF_Clause_instMembershipLiteral___redArg();
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instMembershipLiteral(lean_object* v_00_u03b1_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_box(0);
return v___x_212_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(lean_object* v_inst_213_, lean_object* v_c_214_, lean_object* v_lit_215_, lean_object* v_i_216_){
_start:
{
lean_object* v_atoms_221_; lean_object* v_polarities_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_atoms_221_ = lean_ctor_get(v_c_214_, 0);
v_polarities_222_ = lean_ctor_get(v_c_214_, 1);
v___x_223_ = lean_array_get_size(v_atoms_221_);
v___x_224_ = lean_nat_dec_lt(v_i_216_, v___x_223_);
if (v___x_224_ == 0)
{
lean_dec(v_i_216_);
lean_dec_ref(v_lit_215_);
lean_dec_ref(v_inst_213_);
return v___x_224_;
}
else
{
lean_object* v_fst_225_; lean_object* v_snd_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_fst_225_ = lean_ctor_get(v_lit_215_, 0);
v_snd_226_ = lean_ctor_get(v_lit_215_, 1);
v___x_227_ = lean_array_fget_borrowed(v_atoms_221_, v_i_216_);
lean_inc_ref(v_inst_213_);
lean_inc(v_fst_225_);
lean_inc(v___x_227_);
v___x_228_ = lean_apply_2(v_inst_213_, v___x_227_, v_fst_225_);
v___x_229_ = lean_unbox(v___x_228_);
if (v___x_229_ == 0)
{
goto v___jp_217_;
}
else
{
uint8_t v___x_230_; uint8_t v___x_231_; uint8_t v___x_232_; uint8_t v___x_233_; 
v___x_230_ = lean_byte_array_fget(v_polarities_222_, v_i_216_);
v___x_231_ = 1;
v___x_232_ = lean_uint8_dec_eq(v___x_230_, v___x_231_);
v___x_233_ = lean_unbox(v_snd_226_);
if (v___x_233_ == 0)
{
if (v___x_232_ == 0)
{
lean_dec(v_i_216_);
lean_dec_ref(v_lit_215_);
lean_dec_ref(v_inst_213_);
return v___x_224_;
}
else
{
goto v___jp_217_;
}
}
else
{
if (v___x_232_ == 0)
{
goto v___jp_217_;
}
else
{
lean_dec(v_i_216_);
lean_dec_ref(v_lit_215_);
lean_dec_ref(v_inst_213_);
return v___x_224_;
}
}
}
}
v___jp_217_:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_add(v_i_216_, v___x_218_);
lean_dec(v_i_216_);
v_i_216_ = v___x_219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg___boxed(lean_object* v_inst_234_, lean_object* v_c_235_, lean_object* v_lit_236_, lean_object* v_i_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_234_, v_c_235_, v_lit_236_, v_i_237_);
lean_dec_ref(v_c_235_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go(lean_object* v_00_u03b1_240_, lean_object* v_inst_241_, lean_object* v_c_242_, lean_object* v_lit_243_, lean_object* v_i_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_241_, v_c_242_, v_lit_243_, v_i_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___boxed(lean_object* v_00_u03b1_246_, lean_object* v_inst_247_, lean_object* v_c_248_, lean_object* v_lit_249_, lean_object* v_i_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go(v_00_u03b1_246_, v_inst_247_, v_c_248_, v_lit_249_, v_i_250_);
lean_dec_ref(v_c_248_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_contains___redArg(lean_object* v_inst_253_, lean_object* v_c_254_, lean_object* v_lit_255_){
_start:
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_253_, v_c_254_, v_lit_255_, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_contains___redArg___boxed(lean_object* v_inst_258_, lean_object* v_c_259_, lean_object* v_lit_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Std_Sat_CNF_Clause_contains___redArg(v_inst_258_, v_c_259_, v_lit_260_);
lean_dec_ref(v_c_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_contains(lean_object* v_00_u03b1_263_, lean_object* v_inst_264_, lean_object* v_c_265_, lean_object* v_lit_266_){
_start:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_264_, v_c_265_, v_lit_266_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_contains___boxed(lean_object* v_00_u03b1_269_, lean_object* v_inst_270_, lean_object* v_c_271_, lean_object* v_lit_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Std_Sat_CNF_Clause_contains(v_00_u03b1_269_, v_inst_270_, v_c_271_, v_lit_272_);
lean_dec_ref(v_c_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(lean_object* v_inst_275_, lean_object* v_lit_276_, lean_object* v_c_277_){
_start:
{
lean_object* v___f_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___f_278_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_278_, 0, v_inst_275_);
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v___f_278_, v_c_277_, v_lit_276_, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg___boxed(lean_object* v_inst_281_, lean_object* v_lit_282_, lean_object* v_c_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v_inst_281_, v_lit_282_, v_c_283_);
lean_dec_ref(v_c_283_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq(lean_object* v_00_u03b1_286_, lean_object* v_inst_287_, lean_object* v_lit_288_, lean_object* v_c_289_){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v_inst_287_, v_lit_288_, v_c_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___boxed(lean_object* v_00_u03b1_291_, lean_object* v_inst_292_, lean_object* v_lit_293_, lean_object* v_c_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq(v_00_u03b1_291_, v_inst_292_, v_lit_293_, v_c_294_);
lean_dec_ref(v_c_294_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_297_, lean_object* v_i_298_, lean_object* v_inst_299_, lean_object* v_c_300_, lean_object* v_f_301_, lean_object* v_sz_302_, lean_object* v_____do__lift_303_){
_start:
{
size_t v_i_boxed_304_; size_t v_sz_boxed_305_; lean_object* v_res_306_; 
v_i_boxed_304_ = lean_unbox_usize(v_i_298_);
lean_dec(v_i_298_);
v_sz_boxed_305_ = lean_unbox_usize(v_sz_302_);
lean_dec(v_sz_302_);
v_res_306_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0(v_toPure_297_, v_i_boxed_304_, v_inst_299_, v_c_300_, v_f_301_, v_sz_boxed_305_, v_____do__lift_303_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(lean_object* v_inst_307_, lean_object* v_c_308_, lean_object* v_f_309_, size_t v_sz_310_, size_t v_i_311_, lean_object* v_b_312_){
_start:
{
lean_object* v_toApplicative_313_; lean_object* v_toBind_314_; lean_object* v_toPure_315_; uint8_t v___x_316_; 
v_toApplicative_313_ = lean_ctor_get(v_inst_307_, 0);
v_toBind_314_ = lean_ctor_get(v_inst_307_, 1);
lean_inc(v_toBind_314_);
v_toPure_315_ = lean_ctor_get(v_toApplicative_313_, 1);
lean_inc(v_toPure_315_);
v___x_316_ = lean_usize_dec_lt(v_i_311_, v_sz_310_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_dec(v_toBind_314_);
lean_dec(v_f_309_);
lean_dec_ref(v_c_308_);
lean_dec_ref(v_inst_307_);
v___x_317_ = lean_apply_2(v_toPure_315_, lean_box(0), v_b_312_);
return v___x_317_;
}
else
{
lean_object* v_atoms_318_; lean_object* v_polarities_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___f_322_; lean_object* v___x_323_; uint8_t v___x_324_; uint8_t v___x_325_; uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_atoms_318_ = lean_ctor_get(v_c_308_, 0);
lean_inc_ref(v_atoms_318_);
v_polarities_319_ = lean_ctor_get(v_c_308_, 1);
lean_inc_ref(v_polarities_319_);
v___x_320_ = lean_box_usize(v_i_311_);
v___x_321_ = lean_box_usize(v_sz_310_);
lean_inc(v_f_309_);
v___f_322_ = lean_alloc_closure((void*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_322_, 0, v_toPure_315_);
lean_closure_set(v___f_322_, 1, v___x_320_);
lean_closure_set(v___f_322_, 2, v_inst_307_);
lean_closure_set(v___f_322_, 3, v_c_308_);
lean_closure_set(v___f_322_, 4, v_f_309_);
lean_closure_set(v___f_322_, 5, v___x_321_);
v___x_323_ = lean_array_uget(v_atoms_318_, v_i_311_);
lean_dec_ref(v_atoms_318_);
v___x_324_ = lean_byte_array_uget(v_polarities_319_, v_i_311_);
lean_dec_ref(v_polarities_319_);
v___x_325_ = 1;
v___x_326_ = lean_uint8_dec_eq(v___x_324_, v___x_325_);
v___x_327_ = lean_box(v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_323_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_apply_3(v_f_309_, v___x_328_, lean_box(0), v_b_312_);
v___x_330_ = lean_apply_4(v_toBind_314_, lean_box(0), lean_box(0), v___x_329_, v___f_322_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0(lean_object* v_toPure_331_, size_t v_i_332_, lean_object* v_inst_333_, lean_object* v_c_334_, lean_object* v_f_335_, size_t v_sz_336_, lean_object* v_____do__lift_337_){
_start:
{
if (lean_obj_tag(v_____do__lift_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; 
lean_dec(v_f_335_);
lean_dec_ref(v_c_334_);
lean_dec_ref(v_inst_333_);
v_a_338_ = lean_ctor_get(v_____do__lift_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v_____do__lift_337_, 1);
v___x_339_ = lean_apply_2(v_toPure_331_, lean_box(0), v_a_338_);
return v___x_339_;
}
else
{
lean_object* v_a_340_; size_t v___x_341_; size_t v___x_342_; lean_object* v___x_343_; 
lean_dec(v_toPure_331_);
v_a_340_ = lean_ctor_get(v_____do__lift_337_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v_____do__lift_337_, 1);
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_add(v_i_332_, v___x_341_);
v___x_343_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_333_, v_c_334_, v_f_335_, v_sz_336_, v___x_342_, v_a_340_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___boxed(lean_object* v_inst_344_, lean_object* v_c_345_, lean_object* v_f_346_, lean_object* v_sz_347_, lean_object* v_i_348_, lean_object* v_b_349_){
_start:
{
size_t v_sz_boxed_350_; size_t v_i_boxed_351_; lean_object* v_res_352_; 
v_sz_boxed_350_ = lean_unbox_usize(v_sz_347_);
lean_dec(v_sz_347_);
v_i_boxed_351_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_res_352_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_344_, v_c_345_, v_f_346_, v_sz_boxed_350_, v_i_boxed_351_, v_b_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop(lean_object* v_m_353_, lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_inst_356_, lean_object* v_c_357_, lean_object* v_f_358_, size_t v_sz_359_, size_t v_i_360_, lean_object* v_b_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_356_, v_c_357_, v_f_358_, v_sz_359_, v_i_360_, v_b_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___boxed(lean_object* v_m_363_, lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_inst_366_, lean_object* v_c_367_, lean_object* v_f_368_, lean_object* v_sz_369_, lean_object* v_i_370_, lean_object* v_b_371_){
_start:
{
size_t v_sz_boxed_372_; size_t v_i_boxed_373_; lean_object* v_res_374_; 
v_sz_boxed_372_ = lean_unbox_usize(v_sz_369_);
lean_dec(v_sz_369_);
v_i_boxed_373_ = lean_unbox_usize(v_i_370_);
lean_dec(v_i_370_);
v_res_374_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop(v_m_363_, v_00_u03b1_364_, v_00_u03b2_365_, v_inst_366_, v_c_367_, v_f_368_, v_sz_boxed_372_, v_i_boxed_373_, v_b_371_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_forIn_x27ImplUnsafe___redArg(lean_object* v_inst_375_, lean_object* v_c_376_, lean_object* v_b_377_, lean_object* v_f_378_){
_start:
{
lean_object* v_atoms_379_; size_t v_sz_380_; size_t v___x_381_; lean_object* v___x_382_; 
v_atoms_379_ = lean_ctor_get(v_c_376_, 0);
v_sz_380_ = lean_array_size(v_atoms_379_);
v___x_381_ = ((size_t)0ULL);
v___x_382_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_375_, v_c_376_, v_f_378_, v_sz_380_, v___x_381_, v_b_377_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_forIn_x27ImplUnsafe(lean_object* v_m_383_, lean_object* v_00_u03b1_384_, lean_object* v_00_u03b2_385_, lean_object* v_inst_386_, lean_object* v_c_387_, lean_object* v_b_388_, lean_object* v_f_389_){
_start:
{
lean_object* v_atoms_390_; size_t v_sz_391_; size_t v___x_392_; lean_object* v___x_393_; 
v_atoms_390_ = lean_ctor_get(v_c_387_, 0);
v_sz_391_ = lean_array_size(v_atoms_390_);
v___x_392_ = ((size_t)0ULL);
v___x_393_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_386_, v_c_387_, v_f_389_, v_sz_391_, v___x_392_, v_b_388_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0___boxed(lean_object* v_toPure_394_, lean_object* v_i_395_, lean_object* v_inst_396_, lean_object* v_c_397_, lean_object* v_f_398_, lean_object* v_____do__lift_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0(v_toPure_394_, v_i_395_, v_inst_396_, v_c_397_, v_f_398_, v_____do__lift_399_);
lean_dec(v_i_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg(lean_object* v_inst_401_, lean_object* v_c_402_, lean_object* v_f_403_, lean_object* v_i_404_, lean_object* v_b_405_){
_start:
{
lean_object* v_toApplicative_406_; lean_object* v_atoms_407_; lean_object* v_toBind_408_; lean_object* v_toPure_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v_toApplicative_406_ = lean_ctor_get(v_inst_401_, 0);
v_atoms_407_ = lean_ctor_get(v_c_402_, 0);
v_toBind_408_ = lean_ctor_get(v_inst_401_, 1);
lean_inc(v_toBind_408_);
v_toPure_409_ = lean_ctor_get(v_toApplicative_406_, 1);
lean_inc(v_toPure_409_);
v___x_410_ = lean_array_get_size(v_atoms_407_);
v___x_411_ = lean_nat_dec_lt(v_i_404_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_dec(v_toBind_408_);
lean_dec(v_i_404_);
lean_dec(v_f_403_);
lean_dec_ref(v_c_402_);
lean_dec_ref(v_inst_401_);
v___x_412_ = lean_apply_2(v_toPure_409_, lean_box(0), v_b_405_);
return v___x_412_;
}
else
{
lean_object* v___f_413_; lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_425_; 
lean_inc(v_f_403_);
lean_inc_ref(v_c_402_);
lean_inc(v_i_404_);
v___f_413_ = lean_alloc_closure((void*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_413_, 0, v_toPure_409_);
lean_closure_set(v___f_413_, 1, v_i_404_);
lean_closure_set(v___f_413_, 2, v_inst_401_);
lean_closure_set(v___f_413_, 3, v_c_402_);
lean_closure_set(v___f_413_, 4, v_f_403_);
v___x_414_ = lean_array_fget(v_atoms_407_, v_i_404_);
v___x_415_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_402_, v_i_404_);
lean_dec(v_i_404_);
v_isSharedCheck_425_ = !lean_is_exclusive(v_c_402_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; lean_object* v_unused_427_; 
v_unused_426_ = lean_ctor_get(v_c_402_, 1);
lean_dec(v_unused_426_);
v_unused_427_ = lean_ctor_get(v_c_402_, 0);
lean_dec(v_unused_427_);
v___x_417_ = v_c_402_;
v_isShared_418_ = v_isSharedCheck_425_;
goto v_resetjp_416_;
}
else
{
lean_dec(v_c_402_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_425_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_box(v___x_415_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_419_);
lean_ctor_set(v___x_417_, 0, v___x_414_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_419_);
v___x_421_ = v_reuseFailAlloc_424_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_apply_3(v_f_403_, v___x_421_, lean_box(0), v_b_405_);
v___x_423_ = lean_apply_4(v_toBind_408_, lean_box(0), lean_box(0), v___x_422_, v___f_413_);
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0(lean_object* v_toPure_428_, lean_object* v_i_429_, lean_object* v_inst_430_, lean_object* v_c_431_, lean_object* v_f_432_, lean_object* v_____do__lift_433_){
_start:
{
if (lean_obj_tag(v_____do__lift_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; 
lean_dec(v_f_432_);
lean_dec_ref(v_c_431_);
lean_dec_ref(v_inst_430_);
v_a_434_ = lean_ctor_get(v_____do__lift_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v_____do__lift_433_, 1);
v___x_435_ = lean_apply_2(v_toPure_428_, lean_box(0), v_a_434_);
return v___x_435_;
}
else
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v_toPure_428_);
v_a_436_ = lean_ctor_get(v_____do__lift_433_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v_____do__lift_433_, 1);
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_add(v_i_429_, v___x_437_);
v___x_439_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg(v_inst_430_, v_c_431_, v_f_432_, v___x_438_, v_a_436_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go(lean_object* v_m_440_, lean_object* v_00_u03b1_441_, lean_object* v_00_u03b2_442_, lean_object* v_inst_443_, lean_object* v_c_444_, lean_object* v_f_445_, lean_object* v_i_446_, lean_object* v_b_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg(v_inst_443_, v_c_444_, v_f_445_, v_i_446_, v_b_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop_match__1_splitter___redArg(lean_object* v_____do__lift_449_, lean_object* v_h__1_450_, lean_object* v_h__2_451_){
_start:
{
if (lean_obj_tag(v_____do__lift_449_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; 
lean_dec(v_h__2_451_);
v_a_452_ = lean_ctor_get(v_____do__lift_449_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v_____do__lift_449_, 1);
v___x_453_ = lean_apply_1(v_h__1_450_, v_a_452_);
return v___x_453_;
}
else
{
lean_object* v_a_454_; lean_object* v___x_455_; 
lean_dec(v_h__1_450_);
v_a_454_ = lean_ctor_get(v_____do__lift_449_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v_____do__lift_449_, 1);
v___x_455_ = lean_apply_1(v_h__2_451_, v_a_454_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop_match__1_splitter(lean_object* v_00_u03b2_456_, lean_object* v_motive_457_, lean_object* v_____do__lift_458_, lean_object* v_h__1_459_, lean_object* v_h__2_460_){
_start:
{
if (lean_obj_tag(v_____do__lift_458_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; 
lean_dec(v_h__2_460_);
v_a_461_ = lean_ctor_get(v_____do__lift_458_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v_____do__lift_458_, 1);
v___x_462_ = lean_apply_1(v_h__1_459_, v_a_461_);
return v___x_462_;
}
else
{
lean_object* v_a_463_; lean_object* v___x_464_; 
lean_dec(v_h__1_459_);
v_a_463_ = lean_ctor_get(v_____do__lift_458_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v_____do__lift_458_, 1);
v___x_464_ = lean_apply_1(v_h__2_460_, v_a_463_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_465_, lean_object* v_00_u03b2_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_atoms_470_; size_t v_sz_471_; size_t v___x_472_; lean_object* v___x_473_; 
v_atoms_470_ = lean_ctor_get(v___y_467_, 0);
v_sz_471_ = lean_array_size(v_atoms_470_);
v___x_472_ = ((size_t)0ULL);
v___x_473_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_465_, v___y_467_, v___y_469_, v_sz_471_, v___x_472_, v___y_468_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg(lean_object* v_inst_474_){
_start:
{
lean_object* v___f_475_; 
v___f_475_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_475_, 0, v_inst_474_);
return v___f_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad(lean_object* v_m_476_, lean_object* v_00_u03b1_477_, lean_object* v_inst_478_){
_start:
{
lean_object* v___f_479_; 
v___f_479_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_479_, 0, v_inst_478_);
return v___f_479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_480_, lean_object* v_h__1_481_, lean_object* v_h__2_482_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_484_; 
lean_dec(v_h__2_482_);
v_a_483_ = lean_ctor_get(v_x_480_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v_x_480_, 1);
v___x_484_ = lean_apply_1(v_h__1_481_, v_a_483_);
return v___x_484_;
}
else
{
lean_object* v_a_485_; lean_object* v___x_486_; 
lean_dec(v_h__1_481_);
v_a_485_ = lean_ctor_get(v_x_480_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v_x_480_, 1);
v___x_486_ = lean_apply_1(v_h__2_482_, v_a_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_487_, lean_object* v_motive_488_, lean_object* v_x_489_, lean_object* v_h__1_490_, lean_object* v_h__2_491_){
_start:
{
if (lean_obj_tag(v_x_489_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_493_; 
lean_dec(v_h__2_491_);
v_a_492_ = lean_ctor_get(v_x_489_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v_x_489_, 1);
v___x_493_ = lean_apply_1(v_h__1_490_, v_a_492_);
return v___x_493_;
}
else
{
lean_object* v_a_494_; lean_object* v___x_495_; 
lean_dec(v_h__1_490_);
v_a_494_ = lean_ctor_get(v_x_489_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v_x_489_, 1);
v___x_495_ = lean_apply_1(v_h__2_491_, v_a_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(lean_object* v_inst_496_, lean_object* v_c_497_, lean_object* v_lit_498_, lean_object* v_i_499_, lean_object* v_acc_500_){
_start:
{
lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; uint8_t v___y_505_; lean_object* v_atoms_509_; lean_object* v_polarities_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_atoms_509_ = lean_ctor_get(v_c_497_, 0);
v_polarities_510_ = lean_ctor_get(v_c_497_, 1);
v___x_511_ = lean_array_get_size(v_atoms_509_);
v___x_512_ = lean_nat_dec_lt(v_i_499_, v___x_511_);
if (v___x_512_ == 0)
{
lean_dec(v_i_499_);
lean_dec_ref(v_lit_498_);
lean_dec_ref(v_inst_496_);
return v_acc_500_;
}
else
{
lean_object* v_fst_513_; lean_object* v_snd_514_; lean_object* v_atom_515_; uint8_t v___x_516_; lean_object* v___x_517_; uint8_t v___x_521_; uint8_t v_pol_522_; lean_object* v___x_529_; uint8_t v___x_530_; 
v_fst_513_ = lean_ctor_get(v_lit_498_, 0);
v_snd_514_ = lean_ctor_get(v_lit_498_, 1);
v_atom_515_ = lean_array_fget_borrowed(v_atoms_509_, v_i_499_);
v___x_516_ = lean_byte_array_fget(v_polarities_510_, v_i_499_);
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_521_ = 1;
v_pol_522_ = lean_uint8_dec_eq(v___x_516_, v___x_521_);
lean_inc_ref(v_inst_496_);
lean_inc(v_fst_513_);
lean_inc(v_atom_515_);
v___x_529_ = lean_apply_2(v_inst_496_, v_atom_515_, v_fst_513_);
v___x_530_ = lean_unbox(v___x_529_);
if (v___x_530_ == 0)
{
goto v___jp_523_;
}
else
{
uint8_t v___x_531_; 
v___x_531_ = lean_unbox(v_snd_514_);
if (v___x_531_ == 0)
{
if (v_pol_522_ == 0)
{
goto v___jp_518_;
}
else
{
goto v___jp_523_;
}
}
else
{
if (v_pol_522_ == 0)
{
goto v___jp_523_;
}
else
{
goto v___jp_518_;
}
}
}
v___jp_518_:
{
lean_object* v___x_519_; 
v___x_519_ = lean_nat_add(v_i_499_, v___x_517_);
lean_dec(v_i_499_);
v_i_499_ = v___x_519_;
goto _start;
}
v___jp_523_:
{
lean_object* v_atoms_524_; lean_object* v_polarities_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_atoms_524_ = lean_ctor_get(v_acc_500_, 0);
lean_inc_ref(v_atoms_524_);
v_polarities_525_ = lean_ctor_get(v_acc_500_, 1);
lean_inc_ref(v_polarities_525_);
lean_dec_ref(v_acc_500_);
v___x_526_ = lean_nat_add(v_i_499_, v___x_517_);
lean_dec(v_i_499_);
lean_inc(v_atom_515_);
v___x_527_ = lean_array_push(v_atoms_524_, v_atom_515_);
if (v_pol_522_ == 0)
{
uint8_t v___x_528_; 
v___x_528_ = 0;
v___y_502_ = v___x_527_;
v___y_503_ = v___x_526_;
v___y_504_ = v_polarities_525_;
v___y_505_ = v___x_528_;
goto v___jp_501_;
}
else
{
v___y_502_ = v___x_527_;
v___y_503_ = v___x_526_;
v___y_504_ = v_polarities_525_;
v___y_505_ = v___x_521_;
goto v___jp_501_;
}
}
}
v___jp_501_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_byte_array_push(v___y_504_, v___y_505_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___y_502_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v_i_499_ = v___y_503_;
v_acc_500_ = v___x_507_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg___boxed(lean_object* v_inst_532_, lean_object* v_c_533_, lean_object* v_lit_534_, lean_object* v_i_535_, lean_object* v_acc_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(v_inst_532_, v_c_533_, v_lit_534_, v_i_535_, v_acc_536_);
lean_dec_ref(v_c_533_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go(lean_object* v_00_u03b1_538_, lean_object* v_inst_539_, lean_object* v_c_540_, lean_object* v_lit_541_, lean_object* v_i_542_, lean_object* v_acc_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(v_inst_539_, v_c_540_, v_lit_541_, v_i_542_, v_acc_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___boxed(lean_object* v_00_u03b1_545_, lean_object* v_inst_546_, lean_object* v_c_547_, lean_object* v_lit_548_, lean_object* v_i_549_, lean_object* v_acc_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go(v_00_u03b1_545_, v_inst_546_, v_c_547_, v_lit_548_, v_i_549_, v_acc_550_);
lean_dec_ref(v_c_547_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase___redArg(lean_object* v_inst_552_, lean_object* v_c_553_, lean_object* v_lit_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___redArg___closed__1, &l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1);
v___x_557_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(v_inst_552_, v_c_553_, v_lit_554_, v___x_555_, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase___redArg___boxed(lean_object* v_inst_558_, lean_object* v_c_559_, lean_object* v_lit_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_Sat_CNF_Clause_erase___redArg(v_inst_558_, v_c_559_, v_lit_560_);
lean_dec_ref(v_c_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase(lean_object* v_00_u03b1_562_, lean_object* v_inst_563_, lean_object* v_c_564_, lean_object* v_lit_565_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___redArg___closed__1, &l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1);
v___x_568_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(v_inst_563_, v_c_564_, v_lit_565_, v___x_566_, v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase___boxed(lean_object* v_00_u03b1_569_, lean_object* v_inst_570_, lean_object* v_c_571_, lean_object* v_lit_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_Sat_CNF_Clause_erase(v_00_u03b1_569_, v_inst_570_, v_c_571_, v_lit_572_);
lean_dec_ref(v_c_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_append___redArg(lean_object* v_c1_574_, lean_object* v_c2_575_){
_start:
{
lean_object* v_atoms_576_; lean_object* v_polarities_577_; lean_object* v_atoms_578_; lean_object* v_polarities_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_592_; 
v_atoms_576_ = lean_ctor_get(v_c1_574_, 0);
lean_inc_ref(v_atoms_576_);
v_polarities_577_ = lean_ctor_get(v_c1_574_, 1);
lean_inc_ref(v_polarities_577_);
lean_dec_ref(v_c1_574_);
v_atoms_578_ = lean_ctor_get(v_c2_575_, 0);
v_polarities_579_ = lean_ctor_get(v_c2_575_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_c2_575_);
if (v_isSharedCheck_592_ == 0)
{
v___x_581_ = v_c2_575_;
v_isShared_582_ = v_isSharedCheck_592_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_polarities_579_);
lean_inc(v_atoms_578_);
lean_dec(v_c2_575_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_592_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_583_ = l_Array_append___redArg(v_atoms_576_, v_atoms_578_);
lean_dec_ref(v_atoms_578_);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_byte_array_size(v_polarities_577_);
v___x_586_ = lean_byte_array_size(v_polarities_579_);
v___x_587_ = 0;
v___x_588_ = lean_byte_array_copy_slice(v_polarities_579_, v___x_584_, v_polarities_577_, v___x_585_, v___x_586_, v___x_587_);
lean_dec_ref(v_polarities_579_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v___x_588_);
lean_ctor_set(v___x_581_, 0, v___x_583_);
v___x_590_ = v___x_581_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_append(lean_object* v_00_u03b1_593_, lean_object* v_c1_594_, lean_object* v_c2_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_Sat_CNF_Clause_append___redArg(v_c1_594_, v_c2_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instAppend___redArg(){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = ((lean_object*)(l_Std_Sat_CNF_Clause_instAppend___redArg___closed__0));
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instAppend___redArg___boxed(lean_object* v___dummy_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_Sat_CNF_Clause_instAppend___redArg();
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instAppend(lean_object* v_00_u03b1_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = ((lean_object*)(l_Std_Sat_CNF_Clause_instAppend___redArg___closed__0));
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty___redArg(){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = ((lean_object*)(l_Std_Sat_CNF_empty___redArg___closed__0));
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty___redArg___boxed(lean_object* v___dummy_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_Sat_CNF_empty___redArg();
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty(lean_object* v_00_u03b1_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = ((lean_object*)(l_Std_Sat_CNF_empty___redArg___closed__0));
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg(lean_object* v_n_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_mk_empty_array_with_capacity(v_n_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg___boxed(lean_object* v_n_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Std_Sat_CNF_emptyWithCapacity___redArg(v_n_614_);
lean_dec(v_n_614_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity(lean_object* v_00_u03b1_616_, lean_object* v_n_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_mk_empty_array_with_capacity(v_n_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___boxed(lean_object* v_00_u03b1_619_, lean_object* v_n_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_Sat_CNF_emptyWithCapacity(v_00_u03b1_619_, v_n_620_);
lean_dec(v_n_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add___redArg(lean_object* v_f_622_, lean_object* v_c_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = lean_array_push(v_f_622_, v_c_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add(lean_object* v_00_u03b1_625_, lean_object* v_f_626_, lean_object* v_c_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_array_push(v_f_626_, v_c_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg(lean_object* v_f1_629_, lean_object* v_f2_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Array_append___redArg(v_f1_629_, v_f2_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg___boxed(lean_object* v_f1_632_, lean_object* v_f2_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_Sat_CNF_append___redArg(v_f1_632_, v_f2_633_);
lean_dec_ref(v_f2_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append(lean_object* v_00_u03b1_635_, lean_object* v_f1_636_, lean_object* v_f2_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Array_append___redArg(v_f1_636_, v_f2_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___boxed(lean_object* v_00_u03b1_639_, lean_object* v_f1_640_, lean_object* v_f2_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Std_Sat_CNF_append(v_00_u03b1_639_, v_f1_640_, v_f2_641_);
lean_dec_ref(v_f2_641_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend___redArg(){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = ((lean_object*)(l_Std_Sat_CNF_instAppend___redArg___closed__0));
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend___redArg___boxed(lean_object* v___dummy_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_Sat_CNF_instAppend___redArg();
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend(lean_object* v_00_u03b1_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = ((lean_object*)(l_Std_Sat_CNF_instAppend___redArg___closed__0));
return v___x_649_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg(lean_object* v_v_650_, lean_object* v_c_651_, lean_object* v_inst_652_){
_start:
{
lean_object* v_atoms_653_; lean_object* v___f_654_; uint8_t v___x_655_; 
v_atoms_653_ = lean_ctor_get(v_c_651_, 0);
lean_inc_ref(v_atoms_653_);
lean_dec_ref(v_c_651_);
v___f_654_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_654_, 0, v_inst_652_);
v___x_655_ = l_Array_contains___redArg(v___f_654_, v_atoms_653_, v_v_650_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object* v_v_656_, lean_object* v_c_657_, lean_object* v_inst_658_){
_start:
{
uint8_t v_res_659_; lean_object* v_r_660_; 
v_res_659_ = l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg(v_v_656_, v_c_657_, v_inst_658_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq(lean_object* v_00_u03b1_661_, lean_object* v_v_662_, lean_object* v_c_663_, lean_object* v_inst_664_){
_start:
{
uint8_t v___x_665_; 
v___x_665_ = l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg(v_v_662_, v_c_663_, v_inst_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_666_, lean_object* v_v_667_, lean_object* v_c_668_, lean_object* v_inst_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq(v_00_u03b1_666_, v_v_667_, v_c_668_, v_inst_669_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause___redArg(){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = lean_box(0);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause___redArg___boxed(lean_object* v___dummy_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_Sat_CNF_instMembershipClause___redArg();
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause(lean_object* v_00_u03b1_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = lean_box(0);
return v___x_677_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0(lean_object* v_inst_678_, lean_object* v_a_679_, lean_object* v_b_680_){
_start:
{
uint8_t v___x_681_; 
v___x_681_ = l_Std_Sat_CNF_Clause_instDecidableEq___redArg(v_inst_678_, v_a_679_, v_b_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0___boxed(lean_object* v_inst_682_, lean_object* v_a_683_, lean_object* v_b_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0(v_inst_682_, v_a_683_, v_b_684_);
lean_dec_ref(v_b_684_);
lean_dec_ref(v_a_683_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(lean_object* v_c_687_, lean_object* v_f_688_, lean_object* v_inst_689_){
_start:
{
lean_object* v___f_690_; lean_object* v___f_691_; uint8_t v___x_692_; 
v___f_690_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_690_, 0, v_inst_689_);
v___f_691_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_691_, 0, v___f_690_);
v___x_692_ = l_Array_contains___redArg(v___f_691_, v_f_688_, v_c_687_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___boxed(lean_object* v_c_693_, lean_object* v_f_694_, lean_object* v_inst_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(v_c_693_, v_f_694_, v_inst_695_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(lean_object* v_00_u03b1_698_, lean_object* v_c_699_, lean_object* v_f_700_, lean_object* v_inst_701_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(v_c_699_, v_f_700_, v_inst_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___boxed(lean_object* v_00_u03b1_703_, lean_object* v_c_704_, lean_object* v_f_705_, lean_object* v_inst_706_){
_start:
{
uint8_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(v_00_u03b1_703_, v_c_704_, v_f_705_, v_inst_706_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0(lean_object* v_f_709_, lean_object* v_inst_710_, lean_object* v_v_711_, lean_object* v_i_712_, lean_object* v_h_713_){
_start:
{
lean_object* v___x_714_; lean_object* v_atoms_715_; lean_object* v___f_716_; uint8_t v___x_717_; 
v___x_714_ = lean_array_fget_borrowed(v_f_709_, v_i_712_);
v_atoms_715_ = lean_ctor_get(v___x_714_, 0);
v___f_716_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_716_, 0, v_inst_710_);
lean_inc_ref(v_atoms_715_);
v___x_717_ = l_Array_contains___redArg(v___f_716_, v_atoms_715_, v_v_711_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object* v_f_718_, lean_object* v_inst_719_, lean_object* v_v_720_, lean_object* v_i_721_, lean_object* v_h_722_){
_start:
{
uint8_t v_res_723_; lean_object* v_r_724_; 
v_res_723_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0(v_f_718_, v_inst_719_, v_v_720_, v_i_721_, v_h_722_);
lean_dec(v_i_721_);
lean_dec_ref(v_f_718_);
v_r_724_ = lean_box(v_res_723_);
return v_r_724_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(lean_object* v_v_725_, lean_object* v_f_726_, lean_object* v_inst_727_){
_start:
{
lean_object* v___f_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
lean_inc_ref(v_f_726_);
v___f_728_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_728_, 0, v_f_726_);
lean_closure_set(v___f_728_, 1, v_inst_727_);
lean_closure_set(v___f_728_, 2, v_v_725_);
v___x_729_ = lean_array_get_size(v_f_726_);
lean_dec_ref(v_f_726_);
v___x_730_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(v___x_729_, v___f_728_, v___x_729_, lean_box(0));
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object* v_v_731_, lean_object* v_f_732_, lean_object* v_inst_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(v_v_731_, v_f_732_, v_inst_733_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(lean_object* v_00_u03b1_736_, lean_object* v_v_737_, lean_object* v_f_738_, lean_object* v_inst_739_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(v_v_737_, v_f_738_, v_inst_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_741_, lean_object* v_v_742_, lean_object* v_f_743_, lean_object* v_inst_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(v_00_u03b1_741_, v_v_742_, v_f_743_, v_inst_744_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(uint8_t v___x_747_, lean_object* v_x_748_){
_start:
{
lean_object* v_atoms_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_atoms_749_ = lean_ctor_get(v_x_748_, 0);
v___x_750_ = lean_array_get_size(v_atoms_749_);
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = lean_nat_dec_eq(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
return v___x_747_;
}
else
{
uint8_t v___x_753_; 
v___x_753_ = 0;
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object* v___x_754_, lean_object* v_x_755_){
_start:
{
uint8_t v___x_95__boxed_756_; uint8_t v_res_757_; lean_object* v_r_758_; 
v___x_95__boxed_756_ = lean_unbox(v___x_754_);
v_res_757_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(v___x_95__boxed_756_, v_x_755_);
lean_dec_ref(v_x_755_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(lean_object* v_f_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = lean_array_get_size(v_f_778_);
v___x_781_ = ((lean_object*)(l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9));
v___x_782_ = lean_nat_dec_lt(v___x_779_, v___x_780_);
if (v___x_782_ == 0)
{
lean_dec_ref(v_f_778_);
return v___x_782_;
}
else
{
if (v___x_782_ == 0)
{
lean_dec_ref(v_f_778_);
return v___x_782_;
}
else
{
lean_object* v___x_783_; lean_object* v___f_784_; size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_783_ = lean_box(v___x_782_);
v___f_784_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_784_, 0, v___x_783_);
v___x_785_ = ((size_t)0ULL);
v___x_786_ = lean_usize_of_nat(v___x_780_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_781_, v___f_784_, v_f_778_, v___x_785_, v___x_786_);
v___x_788_ = lean_unbox(v___x_787_);
lean_dec(v___x_787_);
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___boxed(lean_object* v_f_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_789_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(lean_object* v_00_u03b1_792_, lean_object* v_f_793_, lean_object* v_inst_794_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_796_, lean_object* v_f_797_, lean_object* v_inst_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(v_00_u03b1_796_, v_f_797_, v_inst_798_);
lean_dec_ref(v_inst_798_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
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
