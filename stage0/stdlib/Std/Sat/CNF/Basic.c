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
uint8_t l_Std_Sat_CNF_Clause_instDecidableEq___redArg(lean_object* v_inst_1_, lean_object* v_c1_2_, lean_object* v_c2_3_){
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
LEAN_EXPORT void l_Std_Sat_CNF_Clause_instDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_c1_2_ = stack[1].m_obj;
lean_object* v_c2_3_ = stack[2].m_obj;
uint8_t v_res_10_;
v_res_10_ = l_Std_Sat_CNF_Clause_instDecidableEq___redArg(v_inst_1_, v_c1_2_, v_c2_3_);
stack->m_num = v_res_10_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableEq___redArg___boxed(lean_object* v_inst_11_, lean_object* v_c1_12_, lean_object* v_c2_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Std_Sat_CNF_Clause_instDecidableEq___redArg(v_inst_11_, v_c1_12_, v_c2_13_);
lean_dec_ref(v_c2_13_);
lean_dec_ref(v_c1_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
uint8_t l_Std_Sat_CNF_Clause_instDecidableEq(lean_object* v_00_u03b1_16_, lean_object* v_inst_17_, lean_object* v_c1_18_, lean_object* v_c2_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = l_Std_Sat_CNF_Clause_instDecidableEq___redArg(v_inst_17_, v_c1_18_, v_c2_19_);
return v___x_20_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_instDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_17_ = stack[1].m_obj;
lean_object* v_c1_18_ = stack[2].m_obj;
lean_object* v_c2_19_ = stack[3].m_obj;
uint8_t v_res_21_;
v_res_21_ = l_Std_Sat_CNF_Clause_instDecidableEq(lean_box(0), v_inst_17_, v_c1_18_, v_c2_19_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableEq___boxed(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_, lean_object* v_c1_24_, lean_object* v_c2_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Std_Sat_CNF_Clause_instDecidableEq(v_00_u03b1_22_, v_inst_23_, v_c1_24_, v_c2_25_);
lean_dec_ref(v_c2_25_);
lean_dec_ref(v_c1_24_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
static lean_object* _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = l_ByteArray_empty;
v___x_31_ = ((lean_object*)(l_Std_Sat_CNF_Clause_empty___redArg___closed__0));
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___x_30_);
return v___x_32_;
}
}
lean_object* l_Std_Sat_CNF_Clause_empty___redArg(){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___redArg___closed__1, &l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1);
return v___x_34_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_35_;
v_res_35_ = l_Std_Sat_CNF_Clause_empty___redArg();
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_empty___redArg___boxed(lean_object* v___dummy_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Sat_CNF_Clause_empty___redArg();
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_empty(lean_object* v_00_u03b1_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___redArg___closed__1, &l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1);
return v___x_39_;
}
}
lean_object* l_Std_Sat_CNF_Clause_instInhabited___redArg(){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___redArg___closed__1, &l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1);
return v___x_41_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_42_;
v_res_42_ = l_Std_Sat_CNF_Clause_instInhabited___redArg();
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instInhabited___redArg___boxed(lean_object* v___dummy_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Sat_CNF_Clause_instInhabited___redArg();
return v_res_44_;
}
}
static lean_object* _init_l_Std_Sat_CNF_Clause_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Std_Sat_CNF_Clause_instInhabited___redArg();
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instInhabited(lean_object* v_00_u03b1_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_obj_once(&l_Std_Sat_CNF_Clause_instInhabited___closed__0, &l_Std_Sat_CNF_Clause_instInhabited___closed__0_once, _init_l_Std_Sat_CNF_Clause_instInhabited___closed__0);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size___redArg(lean_object* v_c_48_){
_start:
{
lean_object* v_atoms_49_; lean_object* v___x_50_; 
v_atoms_49_ = lean_ctor_get(v_c_48_, 0);
v___x_50_ = lean_array_get_size(v_atoms_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size___redArg___boxed(lean_object* v_c_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Sat_CNF_Clause_size___redArg(v_c_51_);
lean_dec_ref(v_c_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size(lean_object* v_00_u03b1_53_, lean_object* v_c_54_){
_start:
{
lean_object* v_atoms_55_; lean_object* v___x_56_; 
v_atoms_55_ = lean_ctor_get(v_c_54_, 0);
v___x_56_ = lean_array_get_size(v_atoms_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_size___boxed(lean_object* v_00_u03b1_57_, lean_object* v_c_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_Sat_CNF_Clause_size(v_00_u03b1_57_, v_c_58_);
lean_dec_ref(v_c_58_);
return v_res_59_;
}
}
lean_object* l_Std_Sat_CNF_Clause_add___redArg(lean_object* v_c_60_, lean_object* v_atom_61_, uint8_t v_pol_62_){
_start:
{
lean_object* v_atoms_63_; lean_object* v_polarities_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_77_; 
v_atoms_63_ = lean_ctor_get(v_c_60_, 0);
v_polarities_64_ = lean_ctor_get(v_c_60_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v_c_60_);
if (v_isSharedCheck_77_ == 0)
{
v___x_66_ = v_c_60_;
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_polarities_64_);
lean_inc(v_atoms_63_);
lean_dec(v_c_60_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; uint8_t v___y_70_; 
v___x_68_ = lean_array_push(v_atoms_63_, v_atom_61_);
if (v_pol_62_ == 0)
{
uint8_t v___x_75_; 
v___x_75_ = 0;
v___y_70_ = v___x_75_;
goto v___jp_69_;
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 1;
v___y_70_ = v___x_76_;
goto v___jp_69_;
}
v___jp_69_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = lean_byte_array_push(v_polarities_64_, v___y_70_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_71_);
lean_ctor_set(v___x_66_, 0, v___x_68_);
v___x_73_ = v___x_66_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_add___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_60_ = stack[0].m_obj;
lean_object* v_atom_61_ = stack[1].m_obj;
uint8_t v_pol_62_ = stack[2].m_num;
lean_object* v_res_78_;
v_res_78_ = l_Std_Sat_CNF_Clause_add___redArg(v_c_60_, v_atom_61_, v_pol_62_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add___redArg___boxed(lean_object* v_c_79_, lean_object* v_atom_80_, lean_object* v_pol_81_){
_start:
{
uint8_t v_pol_boxed_82_; lean_object* v_res_83_; 
v_pol_boxed_82_ = lean_unbox(v_pol_81_);
v_res_83_ = l_Std_Sat_CNF_Clause_add___redArg(v_c_79_, v_atom_80_, v_pol_boxed_82_);
return v_res_83_;
}
}
lean_object* l_Std_Sat_CNF_Clause_add(lean_object* v_00_u03b1_84_, lean_object* v_c_85_, lean_object* v_atom_86_, uint8_t v_pol_87_){
_start:
{
lean_object* v_atoms_88_; lean_object* v_polarities_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_102_; 
v_atoms_88_ = lean_ctor_get(v_c_85_, 0);
v_polarities_89_ = lean_ctor_get(v_c_85_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v_c_85_);
if (v_isSharedCheck_102_ == 0)
{
v___x_91_ = v_c_85_;
v_isShared_92_ = v_isSharedCheck_102_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_polarities_89_);
lean_inc(v_atoms_88_);
lean_dec(v_c_85_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_102_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; uint8_t v___y_95_; 
v___x_93_ = lean_array_push(v_atoms_88_, v_atom_86_);
if (v_pol_87_ == 0)
{
uint8_t v___x_100_; 
v___x_100_ = 0;
v___y_95_ = v___x_100_;
goto v___jp_94_;
}
else
{
uint8_t v___x_101_; 
v___x_101_ = 1;
v___y_95_ = v___x_101_;
goto v___jp_94_;
}
v___jp_94_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = lean_byte_array_push(v_polarities_89_, v___y_95_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v___x_96_);
lean_ctor_set(v___x_91_, 0, v___x_93_);
v___x_98_ = v___x_91_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_add_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_85_ = stack[1].m_obj;
lean_object* v_atom_86_ = stack[2].m_obj;
uint8_t v_pol_87_ = stack[3].m_num;
lean_object* v_res_103_;
v_res_103_ = l_Std_Sat_CNF_Clause_add(lean_box(0), v_c_85_, v_atom_86_, v_pol_87_);
stack->m_obj
 = v_res_103_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_add___boxed(lean_object* v_00_u03b1_104_, lean_object* v_c_105_, lean_object* v_atom_106_, lean_object* v_pol_107_){
_start:
{
uint8_t v_pol_boxed_108_; lean_object* v_res_109_; 
v_pol_boxed_108_ = lean_unbox(v_pol_107_);
v_res_109_ = l_Std_Sat_CNF_Clause_add(v_00_u03b1_104_, v_c_105_, v_atom_106_, v_pol_boxed_108_);
return v_res_109_;
}
}
uint8_t l_Std_Sat_CNF_Clause_polarity___redArg(lean_object* v_c_110_, lean_object* v_i_111_){
_start:
{
lean_object* v_polarities_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_polarities_112_ = lean_ctor_get(v_c_110_, 1);
v___x_113_ = lean_byte_array_size(v_polarities_112_);
v___x_114_ = lean_nat_dec_lt(v_i_111_, v___x_113_);
if (v___x_114_ == 0)
{
return v___x_114_;
}
else
{
uint8_t v___x_115_; uint8_t v___x_116_; uint8_t v___x_117_; 
v___x_115_ = lean_byte_array_fget(v_polarities_112_, v_i_111_);
v___x_116_ = 1;
v___x_117_ = lean_uint8_dec_eq(v___x_115_, v___x_116_);
return v___x_117_;
}
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_polarity___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_110_ = stack[0].m_obj;
lean_object* v_i_111_ = stack[1].m_obj;
uint8_t v_res_118_;
v_res_118_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_110_, v_i_111_);
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_polarity___redArg___boxed(lean_object* v_c_119_, lean_object* v_i_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_119_, v_i_120_);
lean_dec(v_i_120_);
lean_dec_ref(v_c_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
uint8_t l_Std_Sat_CNF_Clause_polarity(lean_object* v_00_u03b1_123_, lean_object* v_c_124_, lean_object* v_i_125_){
_start:
{
uint8_t v___x_126_; 
v___x_126_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_124_, v_i_125_);
return v___x_126_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_polarity_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_124_ = stack[1].m_obj;
lean_object* v_i_125_ = stack[2].m_obj;
uint8_t v_res_127_;
v_res_127_ = l_Std_Sat_CNF_Clause_polarity(lean_box(0), v_c_124_, v_i_125_);
stack->m_num = v_res_127_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_polarity___boxed(lean_object* v_00_u03b1_128_, lean_object* v_c_129_, lean_object* v_i_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Std_Sat_CNF_Clause_polarity(v_00_u03b1_128_, v_c_129_, v_i_130_);
lean_dec(v_i_130_);
lean_dec_ref(v_c_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(lean_object* v_c_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
if (lean_obj_tag(v_a_134_) == 0)
{
lean_object* v___x_136_; 
v___x_136_ = l_List_reverse___redArg(v_a_135_);
return v___x_136_;
}
else
{
lean_object* v_head_137_; lean_object* v_tail_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_157_; 
v_head_137_ = lean_ctor_get(v_a_134_, 0);
v_tail_138_ = lean_ctor_get(v_a_134_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_a_134_);
if (v_isSharedCheck_157_ == 0)
{
v___x_140_ = v_a_134_;
v_isShared_141_ = v_isSharedCheck_157_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_tail_138_);
lean_inc(v_head_137_);
lean_dec(v_a_134_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_157_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v_fst_142_; lean_object* v_snd_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_156_; 
v_fst_142_ = lean_ctor_get(v_head_137_, 0);
v_snd_143_ = lean_ctor_get(v_head_137_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_head_137_);
if (v_isSharedCheck_156_ == 0)
{
v___x_145_ = v_head_137_;
v_isShared_146_ = v_isSharedCheck_156_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_snd_143_);
lean_inc(v_fst_142_);
lean_dec(v_head_137_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_156_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_147_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_133_, v_snd_143_);
lean_dec(v_snd_143_);
v___x_148_ = lean_box(v___x_147_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_148_);
v___x_150_ = v___x_145_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_fst_142_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v___x_148_);
v___x_150_ = v_reuseFailAlloc_155_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_152_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v_a_135_);
lean_ctor_set(v___x_140_, 0, v___x_150_);
v___x_152_ = v___x_140_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_a_135_);
v___x_152_ = v_reuseFailAlloc_154_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
v_a_134_ = v_tail_138_;
v_a_135_ = v___x_152_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg___boxed(lean_object* v_c_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(v_c_158_, v_a_159_, v_a_160_);
lean_dec_ref(v_c_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_literals___redArg(lean_object* v_c_162_){
_start:
{
lean_object* v_atoms_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_atoms_163_ = lean_ctor_get(v_c_162_, 0);
lean_inc_ref(v_atoms_163_);
v___x_164_ = lean_array_to_list(v_atoms_163_);
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = l_List_zipIdx___redArg(v___x_164_, v___x_165_);
v___x_167_ = lean_box(0);
v___x_168_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(v_c_162_, v___x_166_, v___x_167_);
lean_dec_ref(v_c_162_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_literals(lean_object* v_00_u03b1_169_, lean_object* v_c_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Std_Sat_CNF_Clause_literals___redArg(v_c_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0(lean_object* v_00_u03b1_172_, lean_object* v_c_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___redArg(v_c_173_, v_a_174_, v_a_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0___boxed(lean_object* v_00_u03b1_177_, lean_object* v_c_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_literals_spec__0(v_00_u03b1_177_, v_c_178_, v_a_179_, v_a_180_);
lean_dec_ref(v_c_178_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0___redArg(lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
return v_x_182_;
}
else
{
lean_object* v_head_184_; lean_object* v_tail_185_; lean_object* v_fst_186_; lean_object* v_snd_187_; lean_object* v_atoms_188_; lean_object* v_polarities_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_204_; 
v_head_184_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_head_184_);
v_tail_185_ = lean_ctor_get(v_x_183_, 1);
lean_inc(v_tail_185_);
lean_dec_ref_known(v_x_183_, 2);
v_fst_186_ = lean_ctor_get(v_head_184_, 0);
lean_inc(v_fst_186_);
v_snd_187_ = lean_ctor_get(v_head_184_, 1);
lean_inc(v_snd_187_);
lean_dec(v_head_184_);
v_atoms_188_ = lean_ctor_get(v_x_182_, 0);
v_polarities_189_ = lean_ctor_get(v_x_182_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_182_);
if (v_isSharedCheck_204_ == 0)
{
v___x_191_ = v_x_182_;
v_isShared_192_ = v_isSharedCheck_204_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_polarities_189_);
lean_inc(v_atoms_188_);
lean_dec(v_x_182_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_204_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; uint8_t v___y_195_; uint8_t v___x_201_; 
v___x_193_ = lean_array_push(v_atoms_188_, v_fst_186_);
v___x_201_ = lean_unbox(v_snd_187_);
lean_dec(v_snd_187_);
if (v___x_201_ == 0)
{
uint8_t v___x_202_; 
v___x_202_ = 0;
v___y_195_ = v___x_202_;
goto v___jp_194_;
}
else
{
uint8_t v___x_203_; 
v___x_203_ = 1;
v___y_195_ = v___x_203_;
goto v___jp_194_;
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_196_ = lean_byte_array_push(v_polarities_189_, v___y_195_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_196_);
lean_ctor_set(v___x_191_, 0, v___x_193_);
v___x_198_ = v___x_191_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___x_196_);
v___x_198_ = v_reuseFailAlloc_200_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
v_x_182_ = v___x_198_;
v_x_183_ = v_tail_185_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_ofLiterals___redArg(lean_object* v_l_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___redArg___closed__1, &l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1);
v___x_207_ = l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0___redArg(v___x_206_, v_l_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_ofLiterals(lean_object* v_00_u03b1_208_, lean_object* v_l_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Std_Sat_CNF_Clause_ofLiterals___redArg(v_l_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0(lean_object* v_00_u03b1_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_List_foldl___at___00Std_Sat_CNF_Clause_ofLiterals_spec__0___redArg(v_x_212_, v_x_213_);
return v___x_214_;
}
}
lean_object* l_Std_Sat_CNF_Clause_instMembershipLiteral___redArg(){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_box(0);
return v___x_216_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_instMembershipLiteral___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_217_;
v_res_217_ = l_Std_Sat_CNF_Clause_instMembershipLiteral___redArg();
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instMembershipLiteral___redArg___boxed(lean_object* v___dummy_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_Sat_CNF_Clause_instMembershipLiteral___redArg();
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instMembershipLiteral(lean_object* v_00_u03b1_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_box(0);
return v___x_221_;
}
}
uint8_t l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(lean_object* v_inst_222_, lean_object* v_c_223_, lean_object* v_lit_224_, lean_object* v_i_225_){
_start:
{
lean_object* v_atoms_230_; lean_object* v_polarities_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v_atoms_230_ = lean_ctor_get(v_c_223_, 0);
v_polarities_231_ = lean_ctor_get(v_c_223_, 1);
v___x_232_ = lean_array_get_size(v_atoms_230_);
v___x_233_ = lean_nat_dec_lt(v_i_225_, v___x_232_);
if (v___x_233_ == 0)
{
lean_dec(v_i_225_);
lean_dec_ref(v_lit_224_);
lean_dec_ref(v_inst_222_);
return v___x_233_;
}
else
{
lean_object* v_fst_234_; lean_object* v_snd_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_fst_234_ = lean_ctor_get(v_lit_224_, 0);
v_snd_235_ = lean_ctor_get(v_lit_224_, 1);
v___x_236_ = lean_array_fget_borrowed(v_atoms_230_, v_i_225_);
lean_inc_ref(v_inst_222_);
lean_inc(v_fst_234_);
lean_inc(v___x_236_);
v___x_237_ = lean_apply_2(v_inst_222_, v___x_236_, v_fst_234_);
v___x_238_ = lean_unbox(v___x_237_);
if (v___x_238_ == 0)
{
goto v___jp_226_;
}
else
{
uint8_t v___x_239_; uint8_t v___x_240_; uint8_t v___x_241_; uint8_t v___x_242_; 
v___x_239_ = lean_byte_array_fget(v_polarities_231_, v_i_225_);
v___x_240_ = 1;
v___x_241_ = lean_uint8_dec_eq(v___x_239_, v___x_240_);
v___x_242_ = lean_unbox(v_snd_235_);
if (v___x_242_ == 0)
{
if (v___x_241_ == 0)
{
lean_dec(v_i_225_);
lean_dec_ref(v_lit_224_);
lean_dec_ref(v_inst_222_);
return v___x_233_;
}
else
{
goto v___jp_226_;
}
}
else
{
if (v___x_241_ == 0)
{
goto v___jp_226_;
}
else
{
lean_dec(v_i_225_);
lean_dec_ref(v_lit_224_);
lean_dec_ref(v_inst_222_);
return v___x_233_;
}
}
}
}
v___jp_226_:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_add(v_i_225_, v___x_227_);
lean_dec(v_i_225_);
v_i_225_ = v___x_228_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_222_ = stack[0].m_obj;
lean_object* v_c_223_ = stack[1].m_obj;
lean_object* v_lit_224_ = stack[2].m_obj;
lean_object* v_i_225_ = stack[3].m_obj;
uint8_t v_res_243_;
v_res_243_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_222_, v_c_223_, v_lit_224_, v_i_225_);
stack->m_num = v_res_243_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg___boxed(lean_object* v_inst_244_, lean_object* v_c_245_, lean_object* v_lit_246_, lean_object* v_i_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_244_, v_c_245_, v_lit_246_, v_i_247_);
lean_dec_ref(v_c_245_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
uint8_t l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go(lean_object* v_00_u03b1_250_, lean_object* v_inst_251_, lean_object* v_c_252_, lean_object* v_lit_253_, lean_object* v_i_254_){
_start:
{
uint8_t v___x_255_; 
v___x_255_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_251_, v_c_252_, v_lit_253_, v_i_254_);
return v___x_255_;
}
}
LEAN_EXPORT void l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_251_ = stack[1].m_obj;
lean_object* v_c_252_ = stack[2].m_obj;
lean_object* v_lit_253_ = stack[3].m_obj;
lean_object* v_i_254_ = stack[4].m_obj;
uint8_t v_res_256_;
v_res_256_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go(lean_box(0), v_inst_251_, v_c_252_, v_lit_253_, v_i_254_);
stack->m_num = v_res_256_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___boxed(lean_object* v_00_u03b1_257_, lean_object* v_inst_258_, lean_object* v_c_259_, lean_object* v_lit_260_, lean_object* v_i_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go(v_00_u03b1_257_, v_inst_258_, v_c_259_, v_lit_260_, v_i_261_);
lean_dec_ref(v_c_259_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
uint8_t l_Std_Sat_CNF_Clause_contains___redArg(lean_object* v_inst_264_, lean_object* v_c_265_, lean_object* v_lit_266_){
_start:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_264_, v_c_265_, v_lit_266_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_264_ = stack[0].m_obj;
lean_object* v_c_265_ = stack[1].m_obj;
lean_object* v_lit_266_ = stack[2].m_obj;
uint8_t v_res_269_;
v_res_269_ = l_Std_Sat_CNF_Clause_contains___redArg(v_inst_264_, v_c_265_, v_lit_266_);
stack->m_num = v_res_269_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_contains___redArg___boxed(lean_object* v_inst_270_, lean_object* v_c_271_, lean_object* v_lit_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Std_Sat_CNF_Clause_contains___redArg(v_inst_270_, v_c_271_, v_lit_272_);
lean_dec_ref(v_c_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
uint8_t l_Std_Sat_CNF_Clause_contains(lean_object* v_00_u03b1_275_, lean_object* v_inst_276_, lean_object* v_c_277_, lean_object* v_lit_278_){
_start:
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v_inst_276_, v_c_277_, v_lit_278_, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_276_ = stack[1].m_obj;
lean_object* v_c_277_ = stack[2].m_obj;
lean_object* v_lit_278_ = stack[3].m_obj;
uint8_t v_res_281_;
v_res_281_ = l_Std_Sat_CNF_Clause_contains(lean_box(0), v_inst_276_, v_c_277_, v_lit_278_);
stack->m_num = v_res_281_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_contains___boxed(lean_object* v_00_u03b1_282_, lean_object* v_inst_283_, lean_object* v_c_284_, lean_object* v_lit_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l_Std_Sat_CNF_Clause_contains(v_00_u03b1_282_, v_inst_283_, v_c_284_, v_lit_285_);
lean_dec_ref(v_c_284_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
uint8_t l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(lean_object* v_inst_288_, lean_object* v_lit_289_, lean_object* v_c_290_){
_start:
{
lean_object* v___f_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___f_291_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_291_, 0, v_inst_288_);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_contains_go___redArg(v___f_291_, v_c_290_, v_lit_289_, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_288_ = stack[0].m_obj;
lean_object* v_lit_289_ = stack[1].m_obj;
lean_object* v_c_290_ = stack[2].m_obj;
uint8_t v_res_294_;
v_res_294_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v_inst_288_, v_lit_289_, v_c_290_);
stack->m_num = v_res_294_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg___boxed(lean_object* v_inst_295_, lean_object* v_lit_296_, lean_object* v_c_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v_inst_295_, v_lit_296_, v_c_297_);
lean_dec_ref(v_c_297_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
uint8_t l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq(lean_object* v_00_u03b1_300_, lean_object* v_inst_301_, lean_object* v_lit_302_, lean_object* v_c_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___redArg(v_inst_301_, v_lit_302_, v_c_303_);
return v___x_304_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_301_ = stack[1].m_obj;
lean_object* v_lit_302_ = stack[2].m_obj;
lean_object* v_c_303_ = stack[3].m_obj;
uint8_t v_res_305_;
v_res_305_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq(lean_box(0), v_inst_301_, v_lit_302_, v_c_303_);
stack->m_num = v_res_305_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq___boxed(lean_object* v_00_u03b1_306_, lean_object* v_inst_307_, lean_object* v_lit_308_, lean_object* v_c_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Std_Sat_CNF_Clause_instDecidableMemLiteralOfDecidableEq(v_00_u03b1_306_, v_inst_307_, v_lit_308_, v_c_309_);
lean_dec_ref(v_c_309_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0___boxed(lean_object* v_toPure_312_, lean_object* v_i_313_, lean_object* v_inst_314_, lean_object* v_c_315_, lean_object* v_f_316_, lean_object* v_sz_317_, lean_object* v_____do__lift_318_){
_start:
{
size_t v_i_boxed_319_; size_t v_sz_boxed_320_; lean_object* v_res_321_; 
v_i_boxed_319_ = lean_unbox_usize(v_i_313_);
lean_dec(v_i_313_);
v_sz_boxed_320_ = lean_unbox_usize(v_sz_317_);
lean_dec(v_sz_317_);
v_res_321_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0(v_toPure_312_, v_i_boxed_319_, v_inst_314_, v_c_315_, v_f_316_, v_sz_boxed_320_, v_____do__lift_318_);
return v_res_321_;
}
}
lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(lean_object* v_inst_322_, lean_object* v_c_323_, lean_object* v_f_324_, size_t v_sz_325_, size_t v_i_326_, lean_object* v_b_327_){
_start:
{
lean_object* v_toApplicative_328_; lean_object* v_toBind_329_; lean_object* v_toPure_330_; uint8_t v___x_331_; 
v_toApplicative_328_ = lean_ctor_get(v_inst_322_, 0);
v_toBind_329_ = lean_ctor_get(v_inst_322_, 1);
lean_inc(v_toBind_329_);
v_toPure_330_ = lean_ctor_get(v_toApplicative_328_, 1);
lean_inc(v_toPure_330_);
v___x_331_ = lean_usize_dec_lt(v_i_326_, v_sz_325_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
lean_dec(v_toBind_329_);
lean_dec(v_f_324_);
lean_dec_ref(v_c_323_);
lean_dec_ref(v_inst_322_);
v___x_332_ = lean_apply_2(v_toPure_330_, lean_box(0), v_b_327_);
return v___x_332_;
}
else
{
lean_object* v_atoms_333_; lean_object* v_polarities_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___f_337_; lean_object* v___x_338_; uint8_t v___x_339_; uint8_t v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_atoms_333_ = lean_ctor_get(v_c_323_, 0);
lean_inc_ref(v_atoms_333_);
v_polarities_334_ = lean_ctor_get(v_c_323_, 1);
lean_inc_ref(v_polarities_334_);
v___x_335_ = lean_box_usize(v_i_326_);
v___x_336_ = lean_box_usize(v_sz_325_);
lean_inc(v_f_324_);
v___f_337_ = lean_alloc_closure((void*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_337_, 0, v_toPure_330_);
lean_closure_set(v___f_337_, 1, v___x_335_);
lean_closure_set(v___f_337_, 2, v_inst_322_);
lean_closure_set(v___f_337_, 3, v_c_323_);
lean_closure_set(v___f_337_, 4, v_f_324_);
lean_closure_set(v___f_337_, 5, v___x_336_);
v___x_338_ = lean_array_uget(v_atoms_333_, v_i_326_);
lean_dec_ref(v_atoms_333_);
v___x_339_ = lean_byte_array_uget(v_polarities_334_, v_i_326_);
lean_dec_ref(v_polarities_334_);
v___x_340_ = 1;
v___x_341_ = lean_uint8_dec_eq(v___x_339_, v___x_340_);
v___x_342_ = lean_box(v___x_341_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_338_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_apply_3(v_f_324_, v___x_343_, lean_box(0), v_b_327_);
v___x_345_ = lean_apply_4(v_toBind_329_, lean_box(0), lean_box(0), v___x_344_, v___f_337_);
return v___x_345_;
}
}
}
LEAN_EXPORT void l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_322_ = stack[0].m_obj;
lean_object* v_c_323_ = stack[1].m_obj;
lean_object* v_f_324_ = stack[2].m_obj;
size_t v_sz_325_ = stack[3].m_num;
size_t v_i_326_ = stack[4].m_num;
lean_object* v_b_327_ = stack[5].m_obj;
lean_object* v_res_346_;
v_res_346_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_322_, v_c_323_, v_f_324_, v_sz_325_, v_i_326_, v_b_327_);
stack->m_obj
 = v_res_346_;
}
lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0(lean_object* v_toPure_347_, size_t v_i_348_, lean_object* v_inst_349_, lean_object* v_c_350_, lean_object* v_f_351_, size_t v_sz_352_, lean_object* v_____do__lift_353_){
_start:
{
if (lean_obj_tag(v_____do__lift_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_355_; 
lean_dec(v_f_351_);
lean_dec_ref(v_c_350_);
lean_dec_ref(v_inst_349_);
v_a_354_ = lean_ctor_get(v_____do__lift_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v_____do__lift_353_, 1);
v___x_355_ = lean_apply_2(v_toPure_347_, lean_box(0), v_a_354_);
return v___x_355_;
}
else
{
lean_object* v_a_356_; size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; 
lean_dec(v_toPure_347_);
v_a_356_ = lean_ctor_get(v_____do__lift_353_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v_____do__lift_353_, 1);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_add(v_i_348_, v___x_357_);
v___x_359_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_349_, v_c_350_, v_f_351_, v_sz_352_, v___x_358_, v_a_356_);
return v___x_359_;
}
}
}
LEAN_EXPORT void l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_347_ = stack[0].m_obj;
size_t v_i_348_ = stack[1].m_num;
lean_object* v_inst_349_ = stack[2].m_obj;
lean_object* v_c_350_ = stack[3].m_obj;
lean_object* v_f_351_ = stack[4].m_obj;
size_t v_sz_352_ = stack[5].m_num;
lean_object* v_____do__lift_353_ = stack[6].m_obj;
lean_object* v_res_360_;
v_res_360_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___lam__0(v_toPure_347_, v_i_348_, v_inst_349_, v_c_350_, v_f_351_, v_sz_352_, v_____do__lift_353_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg___boxed(lean_object* v_inst_361_, lean_object* v_c_362_, lean_object* v_f_363_, lean_object* v_sz_364_, lean_object* v_i_365_, lean_object* v_b_366_){
_start:
{
size_t v_sz_boxed_367_; size_t v_i_boxed_368_; lean_object* v_res_369_; 
v_sz_boxed_367_ = lean_unbox_usize(v_sz_364_);
lean_dec(v_sz_364_);
v_i_boxed_368_ = lean_unbox_usize(v_i_365_);
lean_dec(v_i_365_);
v_res_369_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_361_, v_c_362_, v_f_363_, v_sz_boxed_367_, v_i_boxed_368_, v_b_366_);
return v_res_369_;
}
}
lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop(lean_object* v_m_370_, lean_object* v_00_u03b1_371_, lean_object* v_00_u03b2_372_, lean_object* v_inst_373_, lean_object* v_c_374_, lean_object* v_f_375_, size_t v_sz_376_, size_t v_i_377_, lean_object* v_b_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_373_, v_c_374_, v_f_375_, v_sz_376_, v_i_377_, v_b_378_);
return v___x_379_;
}
}
LEAN_EXPORT void l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_373_ = stack[3].m_obj;
lean_object* v_c_374_ = stack[4].m_obj;
lean_object* v_f_375_ = stack[5].m_obj;
size_t v_sz_376_ = stack[6].m_num;
size_t v_i_377_ = stack[7].m_num;
lean_object* v_b_378_ = stack[8].m_obj;
lean_object* v_res_380_;
v_res_380_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_373_, v_c_374_, v_f_375_, v_sz_376_, v_i_377_, v_b_378_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___boxed(lean_object* v_m_381_, lean_object* v_00_u03b1_382_, lean_object* v_00_u03b2_383_, lean_object* v_inst_384_, lean_object* v_c_385_, lean_object* v_f_386_, lean_object* v_sz_387_, lean_object* v_i_388_, lean_object* v_b_389_){
_start:
{
size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_sz_boxed_390_ = lean_unbox_usize(v_sz_387_);
lean_dec(v_sz_387_);
v_i_boxed_391_ = lean_unbox_usize(v_i_388_);
lean_dec(v_i_388_);
v_res_392_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop(v_m_381_, v_00_u03b1_382_, v_00_u03b2_383_, v_inst_384_, v_c_385_, v_f_386_, v_sz_boxed_390_, v_i_boxed_391_, v_b_389_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_forIn_x27ImplUnsafe___redArg(lean_object* v_inst_393_, lean_object* v_c_394_, lean_object* v_b_395_, lean_object* v_f_396_){
_start:
{
lean_object* v_atoms_397_; size_t v_sz_398_; size_t v___x_399_; lean_object* v___x_400_; 
v_atoms_397_ = lean_ctor_get(v_c_394_, 0);
v_sz_398_ = lean_array_size(v_atoms_397_);
v___x_399_ = ((size_t)0ULL);
v___x_400_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_393_, v_c_394_, v_f_396_, v_sz_398_, v___x_399_, v_b_395_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_forIn_x27ImplUnsafe(lean_object* v_m_401_, lean_object* v_00_u03b1_402_, lean_object* v_00_u03b2_403_, lean_object* v_inst_404_, lean_object* v_c_405_, lean_object* v_b_406_, lean_object* v_f_407_){
_start:
{
lean_object* v_atoms_408_; size_t v_sz_409_; size_t v___x_410_; lean_object* v___x_411_; 
v_atoms_408_ = lean_ctor_get(v_c_405_, 0);
v_sz_409_ = lean_array_size(v_atoms_408_);
v___x_410_ = ((size_t)0ULL);
v___x_411_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_404_, v_c_405_, v_f_407_, v_sz_409_, v___x_410_, v_b_406_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0___boxed(lean_object* v_toPure_412_, lean_object* v_i_413_, lean_object* v_inst_414_, lean_object* v_c_415_, lean_object* v_f_416_, lean_object* v_____do__lift_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0(v_toPure_412_, v_i_413_, v_inst_414_, v_c_415_, v_f_416_, v_____do__lift_417_);
lean_dec(v_i_413_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg(lean_object* v_inst_419_, lean_object* v_c_420_, lean_object* v_f_421_, lean_object* v_i_422_, lean_object* v_b_423_){
_start:
{
lean_object* v_toApplicative_424_; lean_object* v_atoms_425_; lean_object* v_toBind_426_; lean_object* v_toPure_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_toApplicative_424_ = lean_ctor_get(v_inst_419_, 0);
v_atoms_425_ = lean_ctor_get(v_c_420_, 0);
v_toBind_426_ = lean_ctor_get(v_inst_419_, 1);
lean_inc(v_toBind_426_);
v_toPure_427_ = lean_ctor_get(v_toApplicative_424_, 1);
lean_inc(v_toPure_427_);
v___x_428_ = lean_array_get_size(v_atoms_425_);
v___x_429_ = lean_nat_dec_lt(v_i_422_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
lean_dec(v_toBind_426_);
lean_dec(v_i_422_);
lean_dec(v_f_421_);
lean_dec_ref(v_c_420_);
lean_dec_ref(v_inst_419_);
v___x_430_ = lean_apply_2(v_toPure_427_, lean_box(0), v_b_423_);
return v___x_430_;
}
else
{
lean_object* v___f_431_; lean_object* v___x_432_; uint8_t v___x_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_443_; 
lean_inc(v_f_421_);
lean_inc_ref(v_c_420_);
lean_inc(v_i_422_);
v___f_431_ = lean_alloc_closure((void*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_431_, 0, v_toPure_427_);
lean_closure_set(v___f_431_, 1, v_i_422_);
lean_closure_set(v___f_431_, 2, v_inst_419_);
lean_closure_set(v___f_431_, 3, v_c_420_);
lean_closure_set(v___f_431_, 4, v_f_421_);
v___x_432_ = lean_array_fget(v_atoms_425_, v_i_422_);
v___x_433_ = l_Std_Sat_CNF_Clause_polarity___redArg(v_c_420_, v_i_422_);
lean_dec(v_i_422_);
v_isSharedCheck_443_ = !lean_is_exclusive(v_c_420_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; lean_object* v_unused_445_; 
v_unused_444_ = lean_ctor_get(v_c_420_, 1);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_c_420_, 0);
lean_dec(v_unused_445_);
v___x_435_ = v_c_420_;
v_isShared_436_ = v_isSharedCheck_443_;
goto v_resetjp_434_;
}
else
{
lean_dec(v_c_420_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_443_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_box(v___x_433_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_437_);
lean_ctor_set(v___x_435_, 0, v___x_432_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_442_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_apply_3(v_f_421_, v___x_439_, lean_box(0), v_b_423_);
v___x_441_ = lean_apply_4(v_toBind_426_, lean_box(0), lean_box(0), v___x_440_, v___f_431_);
return v___x_441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg___lam__0(lean_object* v_toPure_446_, lean_object* v_i_447_, lean_object* v_inst_448_, lean_object* v_c_449_, lean_object* v_f_450_, lean_object* v_____do__lift_451_){
_start:
{
if (lean_obj_tag(v_____do__lift_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; 
lean_dec(v_f_450_);
lean_dec_ref(v_c_449_);
lean_dec_ref(v_inst_448_);
v_a_452_ = lean_ctor_get(v_____do__lift_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v_____do__lift_451_, 1);
v___x_453_ = lean_apply_2(v_toPure_446_, lean_box(0), v_a_452_);
return v___x_453_;
}
else
{
lean_object* v_a_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v_toPure_446_);
v_a_454_ = lean_ctor_get(v_____do__lift_451_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v_____do__lift_451_, 1);
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_add(v_i_447_, v___x_455_);
v___x_457_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg(v_inst_448_, v_c_449_, v_f_450_, v___x_456_, v_a_454_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go(lean_object* v_m_458_, lean_object* v_00_u03b1_459_, lean_object* v_00_u03b2_460_, lean_object* v_inst_461_, lean_object* v_c_462_, lean_object* v_f_463_, lean_object* v_i_464_, lean_object* v_b_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27Impl_go___redArg(v_inst_461_, v_c_462_, v_f_463_, v_i_464_, v_b_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop_match__1_splitter___redArg(lean_object* v_____do__lift_467_, lean_object* v_h__1_468_, lean_object* v_h__2_469_){
_start:
{
if (lean_obj_tag(v_____do__lift_467_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; 
lean_dec(v_h__2_469_);
v_a_470_ = lean_ctor_get(v_____do__lift_467_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v_____do__lift_467_, 1);
v___x_471_ = lean_apply_1(v_h__1_468_, v_a_470_);
return v___x_471_;
}
else
{
lean_object* v_a_472_; lean_object* v___x_473_; 
lean_dec(v_h__1_468_);
v_a_472_ = lean_ctor_get(v_____do__lift_467_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v_____do__lift_467_, 1);
v___x_473_ = lean_apply_1(v_h__2_469_, v_a_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop_match__1_splitter(lean_object* v_00_u03b2_474_, lean_object* v_motive_475_, lean_object* v_____do__lift_476_, lean_object* v_h__1_477_, lean_object* v_h__2_478_){
_start:
{
if (lean_obj_tag(v_____do__lift_476_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
lean_dec(v_h__2_478_);
v_a_479_ = lean_ctor_get(v_____do__lift_476_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v_____do__lift_476_, 1);
v___x_480_ = lean_apply_1(v_h__1_477_, v_a_479_);
return v___x_480_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_482_; 
lean_dec(v_h__1_477_);
v_a_481_ = lean_ctor_get(v_____do__lift_476_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v_____do__lift_476_, 1);
v___x_482_ = lean_apply_1(v_h__2_478_, v_a_481_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_483_, lean_object* v_00_u03b2_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_atoms_488_; size_t v_sz_489_; size_t v___x_490_; lean_object* v___x_491_; 
v_atoms_488_ = lean_ctor_get(v___y_485_, 0);
v_sz_489_ = lean_array_size(v_atoms_488_);
v___x_490_ = ((size_t)0ULL);
v___x_491_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___redArg(v_inst_483_, v___y_485_, v___y_487_, v_sz_489_, v___x_490_, v___y_486_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg(lean_object* v_inst_492_){
_start:
{
lean_object* v___f_493_; 
v___f_493_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_493_, 0, v_inst_492_);
return v___f_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad(lean_object* v_m_494_, lean_object* v_00_u03b1_495_, lean_object* v_inst_496_){
_start:
{
lean_object* v___f_497_; 
v___f_497_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_Clause_instForIn_x27LiteralInferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_497_, 0, v_inst_496_);
return v___f_497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_498_, lean_object* v_h__1_499_, lean_object* v_h__2_500_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_502_; 
lean_dec(v_h__2_500_);
v_a_501_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v_x_498_, 1);
v___x_502_ = lean_apply_1(v_h__1_499_, v_a_501_);
return v___x_502_;
}
else
{
lean_object* v_a_503_; lean_object* v___x_504_; 
lean_dec(v_h__1_499_);
v_a_503_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v_x_498_, 1);
v___x_504_ = lean_apply_1(v_h__2_500_, v_a_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_505_, lean_object* v_motive_506_, lean_object* v_x_507_, lean_object* v_h__1_508_, lean_object* v_h__2_509_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
lean_dec(v_h__2_509_);
v_a_510_ = lean_ctor_get(v_x_507_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v_x_507_, 1);
v___x_511_ = lean_apply_1(v_h__1_508_, v_a_510_);
return v___x_511_;
}
else
{
lean_object* v_a_512_; lean_object* v___x_513_; 
lean_dec(v_h__1_508_);
v_a_512_ = lean_ctor_get(v_x_507_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v_x_507_, 1);
v___x_513_ = lean_apply_1(v_h__2_509_, v_a_512_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(lean_object* v_inst_514_, lean_object* v_c_515_, lean_object* v_lit_516_, lean_object* v_i_517_, lean_object* v_acc_518_){
_start:
{
lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; uint8_t v___y_523_; lean_object* v_atoms_527_; lean_object* v_polarities_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v_atoms_527_ = lean_ctor_get(v_c_515_, 0);
v_polarities_528_ = lean_ctor_get(v_c_515_, 1);
v___x_529_ = lean_array_get_size(v_atoms_527_);
v___x_530_ = lean_nat_dec_lt(v_i_517_, v___x_529_);
if (v___x_530_ == 0)
{
lean_dec(v_i_517_);
lean_dec_ref(v_lit_516_);
lean_dec_ref(v_inst_514_);
return v_acc_518_;
}
else
{
lean_object* v_fst_531_; lean_object* v_snd_532_; lean_object* v_atom_533_; uint8_t v___x_534_; lean_object* v___x_535_; uint8_t v___x_539_; uint8_t v_pol_540_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_fst_531_ = lean_ctor_get(v_lit_516_, 0);
v_snd_532_ = lean_ctor_get(v_lit_516_, 1);
v_atom_533_ = lean_array_fget_borrowed(v_atoms_527_, v_i_517_);
v___x_534_ = lean_byte_array_fget(v_polarities_528_, v_i_517_);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_539_ = 1;
v_pol_540_ = lean_uint8_dec_eq(v___x_534_, v___x_539_);
lean_inc_ref(v_inst_514_);
lean_inc(v_fst_531_);
lean_inc(v_atom_533_);
v___x_547_ = lean_apply_2(v_inst_514_, v_atom_533_, v_fst_531_);
v___x_548_ = lean_unbox(v___x_547_);
if (v___x_548_ == 0)
{
goto v___jp_541_;
}
else
{
uint8_t v___x_549_; 
v___x_549_ = lean_unbox(v_snd_532_);
if (v___x_549_ == 0)
{
if (v_pol_540_ == 0)
{
goto v___jp_536_;
}
else
{
goto v___jp_541_;
}
}
else
{
if (v_pol_540_ == 0)
{
goto v___jp_541_;
}
else
{
goto v___jp_536_;
}
}
}
v___jp_536_:
{
lean_object* v___x_537_; 
v___x_537_ = lean_nat_add(v_i_517_, v___x_535_);
lean_dec(v_i_517_);
v_i_517_ = v___x_537_;
goto _start;
}
v___jp_541_:
{
lean_object* v_atoms_542_; lean_object* v_polarities_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_atoms_542_ = lean_ctor_get(v_acc_518_, 0);
lean_inc_ref(v_atoms_542_);
v_polarities_543_ = lean_ctor_get(v_acc_518_, 1);
lean_inc_ref(v_polarities_543_);
lean_dec_ref(v_acc_518_);
v___x_544_ = lean_nat_add(v_i_517_, v___x_535_);
lean_dec(v_i_517_);
lean_inc(v_atom_533_);
v___x_545_ = lean_array_push(v_atoms_542_, v_atom_533_);
if (v_pol_540_ == 0)
{
uint8_t v___x_546_; 
v___x_546_ = 0;
v___y_520_ = v_polarities_543_;
v___y_521_ = v___x_545_;
v___y_522_ = v___x_544_;
v___y_523_ = v___x_546_;
goto v___jp_519_;
}
else
{
v___y_520_ = v_polarities_543_;
v___y_521_ = v___x_545_;
v___y_522_ = v___x_544_;
v___y_523_ = v___x_539_;
goto v___jp_519_;
}
}
}
v___jp_519_:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_byte_array_push(v___y_520_, v___y_523_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___y_521_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v_i_517_ = v___y_522_;
v_acc_518_ = v___x_525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg___boxed(lean_object* v_inst_550_, lean_object* v_c_551_, lean_object* v_lit_552_, lean_object* v_i_553_, lean_object* v_acc_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(v_inst_550_, v_c_551_, v_lit_552_, v_i_553_, v_acc_554_);
lean_dec_ref(v_c_551_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go(lean_object* v_00_u03b1_556_, lean_object* v_inst_557_, lean_object* v_c_558_, lean_object* v_lit_559_, lean_object* v_i_560_, lean_object* v_acc_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(v_inst_557_, v_c_558_, v_lit_559_, v_i_560_, v_acc_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___boxed(lean_object* v_00_u03b1_563_, lean_object* v_inst_564_, lean_object* v_c_565_, lean_object* v_lit_566_, lean_object* v_i_567_, lean_object* v_acc_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go(v_00_u03b1_563_, v_inst_564_, v_c_565_, v_lit_566_, v_i_567_, v_acc_568_);
lean_dec_ref(v_c_565_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase___redArg(lean_object* v_inst_570_, lean_object* v_c_571_, lean_object* v_lit_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___redArg___closed__1, &l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1);
v___x_575_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(v_inst_570_, v_c_571_, v_lit_572_, v___x_573_, v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase___redArg___boxed(lean_object* v_inst_576_, lean_object* v_c_577_, lean_object* v_lit_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_Sat_CNF_Clause_erase___redArg(v_inst_576_, v_c_577_, v_lit_578_);
lean_dec_ref(v_c_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase(lean_object* v_00_u03b1_580_, lean_object* v_inst_581_, lean_object* v_c_582_, lean_object* v_lit_583_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_obj_once(&l_Std_Sat_CNF_Clause_empty___redArg___closed__1, &l_Std_Sat_CNF_Clause_empty___redArg___closed__1_once, _init_l_Std_Sat_CNF_Clause_empty___redArg___closed__1);
v___x_586_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_erase_go___redArg(v_inst_581_, v_c_582_, v_lit_583_, v___x_584_, v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_erase___boxed(lean_object* v_00_u03b1_587_, lean_object* v_inst_588_, lean_object* v_c_589_, lean_object* v_lit_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_Sat_CNF_Clause_erase(v_00_u03b1_587_, v_inst_588_, v_c_589_, v_lit_590_);
lean_dec_ref(v_c_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_append___redArg(lean_object* v_c1_592_, lean_object* v_c2_593_){
_start:
{
lean_object* v_atoms_594_; lean_object* v_polarities_595_; lean_object* v_atoms_596_; lean_object* v_polarities_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_610_; 
v_atoms_594_ = lean_ctor_get(v_c1_592_, 0);
lean_inc_ref(v_atoms_594_);
v_polarities_595_ = lean_ctor_get(v_c1_592_, 1);
lean_inc_ref(v_polarities_595_);
lean_dec_ref(v_c1_592_);
v_atoms_596_ = lean_ctor_get(v_c2_593_, 0);
v_polarities_597_ = lean_ctor_get(v_c2_593_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_c2_593_);
if (v_isSharedCheck_610_ == 0)
{
v___x_599_ = v_c2_593_;
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_polarities_597_);
lean_inc(v_atoms_596_);
lean_dec(v_c2_593_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_601_ = l_Array_append___redArg(v_atoms_594_, v_atoms_596_);
lean_dec_ref(v_atoms_596_);
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = lean_byte_array_size(v_polarities_595_);
v___x_604_ = lean_byte_array_size(v_polarities_597_);
v___x_605_ = 0;
v___x_606_ = lean_byte_array_copy_slice(v_polarities_597_, v___x_602_, v_polarities_595_, v___x_603_, v___x_604_, v___x_605_);
lean_dec_ref(v_polarities_597_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 1, v___x_606_);
lean_ctor_set(v___x_599_, 0, v___x_601_);
v___x_608_ = v___x_599_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_append(lean_object* v_00_u03b1_611_, lean_object* v_c1_612_, lean_object* v_c2_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_Sat_CNF_Clause_append___redArg(v_c1_612_, v_c2_613_);
return v___x_614_;
}
}
lean_object* l_Std_Sat_CNF_Clause_instAppend___redArg(){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = ((lean_object*)(l_Std_Sat_CNF_Clause_instAppend___redArg___closed__0));
return v___x_617_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_instAppend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_618_;
v_res_618_ = l_Std_Sat_CNF_Clause_instAppend___redArg();
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instAppend___redArg___boxed(lean_object* v___dummy_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_Sat_CNF_Clause_instAppend___redArg();
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instAppend(lean_object* v_00_u03b1_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = ((lean_object*)(l_Std_Sat_CNF_Clause_instAppend___redArg___closed__0));
return v___x_622_;
}
}
lean_object* l_Std_Sat_CNF_empty___redArg(){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = ((lean_object*)(l_Std_Sat_CNF_empty___redArg___closed__0));
return v___x_626_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_627_;
v_res_627_ = l_Std_Sat_CNF_empty___redArg();
stack->m_obj
 = v_res_627_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty___redArg___boxed(lean_object* v___dummy_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_Sat_CNF_empty___redArg();
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_empty(lean_object* v_00_u03b1_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = ((lean_object*)(l_Std_Sat_CNF_empty___redArg___closed__0));
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg(lean_object* v_n_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = lean_mk_empty_array_with_capacity(v_n_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___redArg___boxed(lean_object* v_n_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_Sat_CNF_emptyWithCapacity___redArg(v_n_634_);
lean_dec(v_n_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity(lean_object* v_00_u03b1_636_, lean_object* v_n_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = lean_mk_empty_array_with_capacity(v_n_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_emptyWithCapacity___boxed(lean_object* v_00_u03b1_639_, lean_object* v_n_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_Sat_CNF_emptyWithCapacity(v_00_u03b1_639_, v_n_640_);
lean_dec(v_n_640_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add___redArg(lean_object* v_f_642_, lean_object* v_c_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = lean_array_push(v_f_642_, v_c_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_add(lean_object* v_00_u03b1_645_, lean_object* v_f_646_, lean_object* v_c_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = lean_array_push(v_f_646_, v_c_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg(lean_object* v_f1_649_, lean_object* v_f2_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Array_append___redArg(v_f1_649_, v_f2_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___redArg___boxed(lean_object* v_f1_652_, lean_object* v_f2_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_Sat_CNF_append___redArg(v_f1_652_, v_f2_653_);
lean_dec_ref(v_f2_653_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append(lean_object* v_00_u03b1_655_, lean_object* v_f1_656_, lean_object* v_f2_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Array_append___redArg(v_f1_656_, v_f2_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_append___boxed(lean_object* v_00_u03b1_659_, lean_object* v_f1_660_, lean_object* v_f2_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Std_Sat_CNF_append(v_00_u03b1_659_, v_f1_660_, v_f2_661_);
lean_dec_ref(v_f2_661_);
return v_res_662_;
}
}
lean_object* l_Std_Sat_CNF_instAppend___redArg(){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = ((lean_object*)(l_Std_Sat_CNF_instAppend___redArg___closed__0));
return v___x_665_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_instAppend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_666_;
v_res_666_ = l_Std_Sat_CNF_instAppend___redArg();
stack->m_obj
 = v_res_666_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend___redArg___boxed(lean_object* v___dummy_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_Sat_CNF_instAppend___redArg();
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instAppend(lean_object* v_00_u03b1_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = ((lean_object*)(l_Std_Sat_CNF_instAppend___redArg___closed__0));
return v___x_670_;
}
}
uint8_t l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg(lean_object* v_v_671_, lean_object* v_c_672_, lean_object* v_inst_673_){
_start:
{
lean_object* v_atoms_674_; lean_object* v___f_675_; uint8_t v___x_676_; 
v_atoms_674_ = lean_ctor_get(v_c_672_, 0);
lean_inc_ref(v_atoms_674_);
lean_dec_ref(v_c_672_);
v___f_675_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_675_, 0, v_inst_673_);
v___x_676_ = l_Array_contains___redArg(v___f_675_, v_atoms_674_, v_v_671_);
return v___x_676_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_671_ = stack[0].m_obj;
lean_object* v_c_672_ = stack[1].m_obj;
lean_object* v_inst_673_ = stack[2].m_obj;
uint8_t v_res_677_;
v_res_677_ = l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg(v_v_671_, v_c_672_, v_inst_673_);
stack->m_num = v_res_677_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object* v_v_678_, lean_object* v_c_679_, lean_object* v_inst_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg(v_v_678_, v_c_679_, v_inst_680_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
uint8_t l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq(lean_object* v_00_u03b1_683_, lean_object* v_v_684_, lean_object* v_c_685_, lean_object* v_inst_686_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___redArg(v_v_684_, v_c_685_, v_inst_686_);
return v___x_687_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_684_ = stack[1].m_obj;
lean_object* v_c_685_ = stack[2].m_obj;
lean_object* v_inst_686_ = stack[3].m_obj;
uint8_t v_res_688_;
v_res_688_ = l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq(lean_box(0), v_v_684_, v_c_685_, v_inst_686_);
stack->m_num = v_res_688_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_689_, lean_object* v_v_690_, lean_object* v_c_691_, lean_object* v_inst_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_Std_Sat_CNF_Clause_instDecidableVarMemOfDecidableEq(v_00_u03b1_689_, v_v_690_, v_c_691_, v_inst_692_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
lean_object* l_Std_Sat_CNF_instMembershipClause___redArg(){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = lean_box(0);
return v___x_696_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_instMembershipClause___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_697_;
v_res_697_ = l_Std_Sat_CNF_instMembershipClause___redArg();
stack->m_obj
 = v_res_697_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause___redArg___boxed(lean_object* v___dummy_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_Sat_CNF_instMembershipClause___redArg();
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instMembershipClause(lean_object* v_00_u03b1_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = lean_box(0);
return v___x_701_;
}
}
uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0(lean_object* v_inst_702_, lean_object* v_a_703_, lean_object* v_b_704_){
_start:
{
uint8_t v___x_705_; 
v___x_705_ = l_Std_Sat_CNF_Clause_instDecidableEq___redArg(v_inst_702_, v_a_703_, v_b_704_);
return v___x_705_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_702_ = stack[0].m_obj;
lean_object* v_a_703_ = stack[1].m_obj;
lean_object* v_b_704_ = stack[2].m_obj;
uint8_t v_res_706_;
v_res_706_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0(v_inst_702_, v_a_703_, v_b_704_);
stack->m_num = v_res_706_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0___boxed(lean_object* v_inst_707_, lean_object* v_a_708_, lean_object* v_b_709_){
_start:
{
uint8_t v_res_710_; lean_object* v_r_711_; 
v_res_710_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0(v_inst_707_, v_a_708_, v_b_709_);
lean_dec_ref(v_b_709_);
lean_dec_ref(v_a_708_);
v_r_711_ = lean_box(v_res_710_);
return v_r_711_;
}
}
uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(lean_object* v_c_712_, lean_object* v_f_713_, lean_object* v_inst_714_){
_start:
{
lean_object* v___f_715_; lean_object* v___f_716_; uint8_t v___x_717_; 
v___f_715_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_715_, 0, v_inst_714_);
v___f_716_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_716_, 0, v___f_715_);
v___x_717_ = l_Array_contains___redArg(v___f_716_, v_f_713_, v_c_712_);
return v___x_717_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_712_ = stack[0].m_obj;
lean_object* v_f_713_ = stack[1].m_obj;
lean_object* v_inst_714_ = stack[2].m_obj;
uint8_t v_res_718_;
v_res_718_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(v_c_712_, v_f_713_, v_inst_714_);
stack->m_num = v_res_718_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg___boxed(lean_object* v_c_719_, lean_object* v_f_720_, lean_object* v_inst_721_){
_start:
{
uint8_t v_res_722_; lean_object* v_r_723_; 
v_res_722_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(v_c_719_, v_f_720_, v_inst_721_);
v_r_723_ = lean_box(v_res_722_);
return v_r_723_;
}
}
uint8_t l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(lean_object* v_00_u03b1_724_, lean_object* v_c_725_, lean_object* v_f_726_, lean_object* v_inst_727_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___redArg(v_c_725_, v_f_726_, v_inst_727_);
return v___x_728_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_725_ = stack[1].m_obj;
lean_object* v_f_726_ = stack[2].m_obj;
lean_object* v_inst_727_ = stack[3].m_obj;
uint8_t v_res_729_;
v_res_729_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(lean_box(0), v_c_725_, v_f_726_, v_inst_727_);
stack->m_num = v_res_729_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq___boxed(lean_object* v_00_u03b1_730_, lean_object* v_c_731_, lean_object* v_f_732_, lean_object* v_inst_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_Std_Sat_CNF_instDecidableMemClauseOfDecidableEq(v_00_u03b1_730_, v_c_731_, v_f_732_, v_inst_733_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0(lean_object* v_f_736_, lean_object* v_inst_737_, lean_object* v_v_738_, lean_object* v_i_739_, lean_object* v_h_740_){
_start:
{
lean_object* v___x_741_; lean_object* v_atoms_742_; lean_object* v___f_743_; uint8_t v___x_744_; 
v___x_741_ = lean_array_fget_borrowed(v_f_736_, v_i_739_);
v_atoms_742_ = lean_ctor_get(v___x_741_, 0);
v___f_743_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_743_, 0, v_inst_737_);
lean_inc_ref(v_atoms_742_);
v___x_744_ = l_Array_contains___redArg(v___f_743_, v_atoms_742_, v_v_738_);
return v___x_744_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_736_ = stack[0].m_obj;
lean_object* v_inst_737_ = stack[1].m_obj;
lean_object* v_v_738_ = stack[2].m_obj;
lean_object* v_i_739_ = stack[3].m_obj;
uint8_t v_res_745_;
v_res_745_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0(v_f_736_, v_inst_737_, v_v_738_, v_i_739_, lean_box(0));
stack->m_num = v_res_745_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object* v_f_746_, lean_object* v_inst_747_, lean_object* v_v_748_, lean_object* v_i_749_, lean_object* v_h_750_){
_start:
{
uint8_t v_res_751_; lean_object* v_r_752_; 
v_res_751_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0(v_f_746_, v_inst_747_, v_v_748_, v_i_749_, v_h_750_);
lean_dec(v_i_749_);
lean_dec_ref(v_f_746_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(lean_object* v_v_753_, lean_object* v_f_754_, lean_object* v_inst_755_){
_start:
{
lean_object* v___f_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
lean_inc_ref(v_f_754_);
v___f_756_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_756_, 0, v_f_754_);
lean_closure_set(v___f_756_, 1, v_inst_755_);
lean_closure_set(v___f_756_, 2, v_v_753_);
v___x_757_ = lean_array_get_size(v_f_754_);
lean_dec_ref(v_f_754_);
v___x_758_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(v___x_757_, v___f_756_, v___x_757_, lean_box(0));
return v___x_758_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_753_ = stack[0].m_obj;
lean_object* v_f_754_ = stack[1].m_obj;
lean_object* v_inst_755_ = stack[2].m_obj;
uint8_t v_res_759_;
v_res_759_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(v_v_753_, v_f_754_, v_inst_755_);
stack->m_num = v_res_759_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg___boxed(lean_object* v_v_760_, lean_object* v_f_761_, lean_object* v_inst_762_){
_start:
{
uint8_t v_res_763_; lean_object* v_r_764_; 
v_res_763_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(v_v_760_, v_f_761_, v_inst_762_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
uint8_t l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(lean_object* v_00_u03b1_765_, lean_object* v_v_766_, lean_object* v_f_767_, lean_object* v_inst_768_){
_start:
{
uint8_t v___x_769_; 
v___x_769_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___redArg(v_v_766_, v_f_767_, v_inst_768_);
return v___x_769_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_766_ = stack[1].m_obj;
lean_object* v_f_767_ = stack[2].m_obj;
lean_object* v_inst_768_ = stack[3].m_obj;
uint8_t v_res_770_;
v_res_770_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(lean_box(0), v_v_766_, v_f_767_, v_inst_768_);
stack->m_num = v_res_770_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_771_, lean_object* v_v_772_, lean_object* v_f_773_, lean_object* v_inst_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l_Std_Sat_CNF_instDecidableVarMemOfDecidableEq(v_00_u03b1_771_, v_v_772_, v_f_773_, v_inst_774_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(uint8_t v___x_777_, lean_object* v_x_778_){
_start:
{
lean_object* v_atoms_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_atoms_779_ = lean_ctor_get(v_x_778_, 0);
v___x_780_ = lean_array_get_size(v_atoms_779_);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_nat_dec_eq(v___x_780_, v___x_781_);
if (v___x_782_ == 0)
{
return v___x_777_;
}
else
{
uint8_t v___x_783_; 
v___x_783_ = 0;
return v___x_783_;
}
}
}
LEAN_EXPORT void l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_777_ = stack[0].m_num;
lean_object* v_x_778_ = stack[1].m_obj;
uint8_t v_res_784_;
v_res_784_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(v___x_777_, v_x_778_);
stack->m_num = v_res_784_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed(lean_object* v___x_785_, lean_object* v_x_786_){
_start:
{
uint8_t v___x_95__boxed_787_; uint8_t v_res_788_; lean_object* v_r_789_; 
v___x_95__boxed_787_ = lean_unbox(v___x_785_);
v_res_788_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0(v___x_95__boxed_787_, v_x_786_);
lean_dec_ref(v_x_786_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(lean_object* v_f_809_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_array_get_size(v_f_809_);
v___x_812_ = ((lean_object*)(l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___closed__9));
v___x_813_ = lean_nat_dec_lt(v___x_810_, v___x_811_);
if (v___x_813_ == 0)
{
lean_dec_ref(v_f_809_);
return v___x_813_;
}
else
{
if (v___x_813_ == 0)
{
lean_dec_ref(v_f_809_);
return v___x_813_;
}
else
{
lean_object* v___x_814_; lean_object* v___f_815_; size_t v___x_816_; size_t v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_814_ = lean_box(v___x_813_);
v___f_815_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_815_, 0, v___x_814_);
v___x_816_ = ((size_t)0ULL);
v___x_817_ = lean_usize_of_nat(v___x_811_);
v___x_818_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_812_, v___f_815_, v_f_809_, v___x_816_, v___x_817_);
v___x_819_ = lean_unbox(v___x_818_);
lean_dec(v___x_818_);
return v___x_819_;
}
}
}
}
LEAN_EXPORT void l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_809_ = stack[0].m_obj;
uint8_t v_res_820_;
v_res_820_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_809_);
stack->m_num = v_res_820_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg___boxed(lean_object* v_f_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_821_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(lean_object* v_00_u03b1_824_, lean_object* v_f_825_, lean_object* v_inst_826_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_825_);
return v___x_827_;
}
}
LEAN_EXPORT void l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_825_ = stack[1].m_obj;
lean_object* v_inst_826_ = stack[2].m_obj;
uint8_t v_res_828_;
v_res_828_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(lean_box(0), v_f_825_, v_inst_826_);
stack->m_num = v_res_828_;
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___boxed(lean_object* v_00_u03b1_829_, lean_object* v_f_830_, lean_object* v_inst_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq(v_00_u03b1_829_, v_f_830_, v_inst_831_);
lean_dec_ref(v_inst_831_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
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
