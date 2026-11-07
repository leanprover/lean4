// Lean compiler output
// Module: Lean.Meta.AbstractNestedProofs
// Imports: public import Init.Grind.Util public import Lean.Meta.Closure public import Lean.Meta.Transform
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
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withoutExporting___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_getLambdaBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_getLambdaBody___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(uint8_t, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nestedProof"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 29, 19, 223, 104, 218, 25)}};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "abstract nested proofs"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_visit___closed__0 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_abstractNestedProofs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_abstractNestedProofs___closed__0;
static lean_once_cell_t l_Lean_Meta_abstractNestedProofs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_abstractNestedProofs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__0(lean_object* v_proof_1_, uint8_t v___x_2_, lean_object* v_inst_3_, uint8_t v_cache_4_, lean_object* v_type_5_){
_start:
{
uint8_t v___y_7_; 
if (v_cache_4_ == 0)
{
v___y_7_ = v_cache_4_;
goto v___jp_6_;
}
else
{
uint8_t v___x_13_; 
v___x_13_ = l_Lean_Expr_hasSorry(v_proof_1_);
if (v___x_13_ == 0)
{
v___y_7_ = v_cache_4_;
goto v___jp_6_;
}
else
{
uint8_t v___x_14_; 
v___x_14_ = 0;
v___y_7_ = v___x_14_;
goto v___jp_6_;
}
}
v___jp_6_:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_8_ = lean_box(0);
v___x_9_ = lean_box(v___x_2_);
v___x_10_ = lean_box(v___y_7_);
v___x_11_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxTheorem___boxed), 10, 5);
lean_closure_set(v___x_11_, 0, v_type_5_);
lean_closure_set(v___x_11_, 1, v_proof_1_);
lean_closure_set(v___x_11_, 2, v___x_9_);
lean_closure_set(v___x_11_, 3, v___x_8_);
lean_closure_set(v___x_11_, 4, v___x_10_);
v___x_12_ = lean_apply_2(v_inst_3_, lean_box(0), v___x_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__0___boxed(lean_object* v_proof_15_, lean_object* v___x_16_, lean_object* v_inst_17_, lean_object* v_cache_18_, lean_object* v_type_19_){
_start:
{
uint8_t v___x_151__boxed_20_; uint8_t v_cache_boxed_21_; lean_object* v_res_22_; 
v___x_151__boxed_20_ = lean_unbox(v___x_16_);
v_cache_boxed_21_ = lean_unbox(v_cache_18_);
v_res_22_ = l_Lean_Meta_abstractProof___redArg___lam__0(v_proof_15_, v___x_151__boxed_20_, v_inst_17_, v_cache_boxed_21_, v_type_19_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__1(lean_object* v_postprocessType_23_, lean_object* v_toBind_24_, lean_object* v___f_25_, lean_object* v_type_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_apply_1(v_postprocessType_23_, v_type_26_);
v___x_28_ = lean_apply_4(v_toBind_24_, lean_box(0), lean_box(0), v___x_27_, v___f_25_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__2(uint8_t v___x_29_, lean_object* v_inst_30_, lean_object* v_toBind_31_, lean_object* v___f_32_, lean_object* v_type_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_34_ = lean_box(v___x_29_);
v___x_35_ = lean_box(v___x_29_);
v___x_36_ = lean_box(v___x_29_);
v___x_37_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___boxed), 9, 4);
lean_closure_set(v___x_37_, 0, v_type_33_);
lean_closure_set(v___x_37_, 1, v___x_34_);
lean_closure_set(v___x_37_, 2, v___x_35_);
lean_closure_set(v___x_37_, 3, v___x_36_);
v___x_38_ = lean_apply_2(v_inst_30_, lean_box(0), v___x_37_);
v___x_39_ = lean_apply_4(v_toBind_31_, lean_box(0), lean_box(0), v___x_38_, v___f_32_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__2___boxed(lean_object* v___x_40_, lean_object* v_inst_41_, lean_object* v_toBind_42_, lean_object* v___f_43_, lean_object* v_type_44_){
_start:
{
uint8_t v___x_181__boxed_45_; lean_object* v_res_46_; 
v___x_181__boxed_45_ = lean_unbox(v___x_40_);
v_res_46_ = l_Lean_Meta_abstractProof___redArg___lam__2(v___x_181__boxed_45_, v_inst_41_, v_toBind_42_, v___f_43_, v_type_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__3(lean_object* v_type_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Core_betaReduce(v_type_47_, v___y_50_, v___y_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__3___boxed(lean_object* v_type_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_abstractProof___redArg___lam__3(v_type_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__4(lean_object* v_inst_61_, lean_object* v_toBind_62_, lean_object* v___f_63_, lean_object* v_type_64_){
_start:
{
lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___f_65_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__3___boxed), 6, 1);
lean_closure_set(v___f_65_, 0, v_type_64_);
v___x_66_ = lean_apply_2(v_inst_61_, lean_box(0), v___f_65_);
v___x_67_ = lean_apply_4(v_toBind_62_, lean_box(0), lean_box(0), v___x_66_, v___f_63_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg(lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_proof_72_, uint8_t v_cache_73_, lean_object* v_postprocessType_74_){
_start:
{
lean_object* v_toBind_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_toBind_75_ = lean_ctor_get(v_inst_68_, 1);
lean_inc_n(v_toBind_75_, 4);
lean_inc_ref(v_proof_72_);
v___x_76_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_76_, 0, v_proof_72_);
lean_inc_n(v_inst_69_, 3);
v___x_77_ = lean_apply_2(v_inst_69_, lean_box(0), v___x_76_);
v___x_78_ = 1;
v___x_79_ = lean_box(v___x_78_);
v___x_80_ = lean_box(v_cache_73_);
v___f_81_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_81_, 0, v_proof_72_);
lean_closure_set(v___f_81_, 1, v___x_79_);
lean_closure_set(v___f_81_, 2, v_inst_69_);
lean_closure_set(v___f_81_, 3, v___x_80_);
v___f_82_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__1), 4, 3);
lean_closure_set(v___f_82_, 0, v_postprocessType_74_);
lean_closure_set(v___f_82_, 1, v_toBind_75_);
lean_closure_set(v___f_82_, 2, v___f_81_);
v___x_83_ = lean_box(v___x_78_);
v___f_84_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_84_, 0, v___x_83_);
lean_closure_set(v___f_84_, 1, v_inst_69_);
lean_closure_set(v___f_84_, 2, v_toBind_75_);
lean_closure_set(v___f_84_, 3, v___f_82_);
v___f_85_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__4), 4, 3);
lean_closure_set(v___f_85_, 0, v_inst_69_);
lean_closure_set(v___f_85_, 1, v_toBind_75_);
lean_closure_set(v___f_85_, 2, v___f_84_);
v___x_86_ = l_Lean_withoutExporting___redArg(v_inst_68_, v_inst_70_, v_inst_71_, v___x_77_, v___x_78_);
v___x_87_ = lean_apply_4(v_toBind_75_, lean_box(0), lean_box(0), v___x_86_, v___f_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___boxed(lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_proof_92_, lean_object* v_cache_93_, lean_object* v_postprocessType_94_){
_start:
{
uint8_t v_cache_boxed_95_; lean_object* v_res_96_; 
v_cache_boxed_95_ = lean_unbox(v_cache_93_);
v_res_96_ = l_Lean_Meta_abstractProof___redArg(v_inst_88_, v_inst_89_, v_inst_90_, v_inst_91_, v_proof_92_, v_cache_boxed_95_, v_postprocessType_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof(lean_object* v_m_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_proof_103_, uint8_t v_cache_104_, lean_object* v_postprocessType_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_abstractProof___redArg(v_inst_98_, v_inst_99_, v_inst_100_, v_inst_102_, v_proof_103_, v_cache_104_, v_postprocessType_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___boxed(lean_object* v_m_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_proof_113_, lean_object* v_cache_114_, lean_object* v_postprocessType_115_){
_start:
{
uint8_t v_cache_boxed_116_; lean_object* v_res_117_; 
v_cache_boxed_116_ = lean_unbox(v_cache_114_);
v_res_117_ = l_Lean_Meta_abstractProof(v_m_107_, v_inst_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_proof_113_, v_cache_boxed_116_, v_postprocessType_115_);
lean_dec_ref(v_inst_111_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_getLambdaBody(lean_object* v_e_118_){
_start:
{
if (lean_obj_tag(v_e_118_) == 6)
{
lean_object* v_body_119_; 
v_body_119_ = lean_ctor_get(v_e_118_, 2);
v_e_118_ = v_body_119_;
goto _start;
}
else
{
lean_inc_ref(v_e_118_);
return v_e_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_getLambdaBody___boxed(lean_object* v_e_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Meta_AbstractNestedProofs_getLambdaBody(v_e_121_);
lean_dec_ref(v_e_121_);
return v_res_122_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(uint8_t v_a_123_, uint8_t v___x_124_, lean_object* v_as_125_, size_t v_i_126_, size_t v_stop_127_){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = lean_usize_dec_eq(v_i_126_, v_stop_127_);
if (v___x_128_ == 0)
{
uint8_t v___x_129_; uint8_t v___y_131_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_129_ = 1;
v___x_135_ = lean_array_uget_borrowed(v_as_125_, v_i_126_);
v___x_136_ = l_Lean_Expr_isAtomic(v___x_135_);
if (v___x_136_ == 0)
{
v___y_131_ = v_a_123_;
goto v___jp_130_;
}
else
{
v___y_131_ = v___x_124_;
goto v___jp_130_;
}
v___jp_130_:
{
if (v___y_131_ == 0)
{
size_t v___x_132_; size_t v___x_133_; 
v___x_132_ = ((size_t)1ULL);
v___x_133_ = lean_usize_add(v_i_126_, v___x_132_);
v_i_126_ = v___x_133_;
goto _start;
}
else
{
return v___x_129_;
}
}
}
else
{
uint8_t v___x_137_; 
v___x_137_ = 0;
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0___boxed(lean_object* v_a_138_, lean_object* v___x_139_, lean_object* v_as_140_, lean_object* v_i_141_, lean_object* v_stop_142_){
_start:
{
uint8_t v_a_4526__boxed_143_; uint8_t v___x_4527__boxed_144_; size_t v_i_boxed_145_; size_t v_stop_boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v_a_4526__boxed_143_ = lean_unbox(v_a_138_);
v___x_4527__boxed_144_ = lean_unbox(v___x_139_);
v_i_boxed_145_ = lean_unbox_usize(v_i_141_);
lean_dec(v_i_141_);
v_stop_boxed_146_ = lean_unbox_usize(v_stop_142_);
lean_dec(v_stop_142_);
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_4526__boxed_143_, v___x_4527__boxed_144_, v_as_140_, v_i_boxed_145_, v_stop_boxed_146_);
lean_dec_ref(v_as_140_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(uint8_t v_a_149_, uint8_t v___x_150_, lean_object* v___x_151_, lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_152_) == 5)
{
lean_object* v_fn_169_; lean_object* v_arg_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_fn_169_ = lean_ctor_get(v_x_152_, 0);
lean_inc_ref(v_fn_169_);
v_arg_170_ = lean_ctor_get(v_x_152_, 1);
lean_inc_ref(v_arg_170_);
lean_dec_ref_known(v_x_152_, 2);
v___x_171_ = lean_array_set(v_x_153_, v_x_154_, v_arg_170_);
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_nat_sub(v_x_154_, v___x_172_);
lean_dec(v_x_154_);
v_x_152_ = v_fn_169_;
v_x_153_ = v___x_171_;
v_x_154_ = v___x_173_;
goto _start;
}
else
{
uint8_t v___x_175_; 
lean_dec(v_x_154_);
v___x_175_ = l_Lean_Expr_isAtomic(v_x_152_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec_ref(v_x_153_);
lean_dec_ref(v_x_152_);
lean_dec_ref(v___x_151_);
v___x_176_ = lean_box(v_a_149_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
else
{
if (v___x_150_ == 0)
{
if (lean_obj_tag(v_x_152_) == 4)
{
lean_object* v_declName_178_; uint8_t v___x_179_; 
v_declName_178_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_declName_178_);
lean_dec_ref_known(v_x_152_, 2);
v___x_179_ = l_Lean_Environment_contains(v___x_151_, v_declName_178_, v_a_149_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec_ref(v_x_153_);
v___x_180_ = lean_box(v_a_149_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
else
{
goto v___jp_156_;
}
}
else
{
lean_dec_ref(v_x_152_);
lean_dec_ref(v___x_151_);
goto v___jp_156_;
}
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec_ref(v_x_153_);
lean_dec_ref(v_x_152_);
lean_dec_ref(v___x_151_);
v___x_182_ = lean_box(v_a_149_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
}
v___jp_156_:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_array_get_size(v_x_153_);
v___x_159_ = lean_nat_dec_lt(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec_ref(v_x_153_);
v___x_160_ = lean_box(v___x_159_);
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
else
{
if (v___x_159_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec_ref(v_x_153_);
v___x_162_ = lean_box(v___x_159_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
else
{
size_t v___x_164_; size_t v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = ((size_t)0ULL);
v___x_165_ = lean_usize_of_nat(v___x_158_);
v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_149_, v___x_150_, v_x_153_, v___x_164_, v___x_165_);
lean_dec_ref(v_x_153_);
v___x_167_ = lean_box(v___x_166_);
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg___boxed(lean_object* v_a_184_, lean_object* v___x_185_, lean_object* v___x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v___y_190_){
_start:
{
uint8_t v_a_4552__boxed_191_; uint8_t v___x_4553__boxed_192_; lean_object* v_res_193_; 
v_a_4552__boxed_191_ = lean_unbox(v_a_184_);
v___x_4553__boxed_192_ = lean_unbox(v___x_185_);
v_res_193_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_a_4552__boxed_191_, v___x_4553__boxed_192_, v___x_186_, v_x_187_, v_x_188_, v_x_189_);
return v_res_193_;
}
}
static lean_object* _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4(void){
_start:
{
lean_object* v___x_201_; lean_object* v_dummy_202_; 
v___x_201_ = lean_box(0);
v_dummy_202_ = l_Lean_Expr_sort___override(v___x_201_);
return v_dummy_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(lean_object* v_e_203_, lean_object* v_env_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; 
lean_inc_ref(v_e_203_);
v___x_210_ = l_Lean_Meta_isProof(v_e_203_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; uint8_t v___x_212_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v___x_212_ = lean_unbox(v_a_211_);
if (v___x_212_ == 0)
{
lean_dec_ref(v_env_204_);
lean_dec_ref(v_e_203_);
return v___x_210_;
}
else
{
lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_231_; 
lean_inc(v_a_211_);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; 
v_unused_232_ = lean_ctor_get(v___x_210_, 0);
lean_dec(v_unused_232_);
v___x_214_ = v___x_210_;
v_isShared_215_ = v_isSharedCheck_231_;
goto v_resetjp_213_;
}
else
{
lean_dec(v___x_210_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_231_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3));
v___x_217_ = l_Lean_Expr_isAppOf(v_e_203_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v_dummy_219_; lean_object* v_nargs_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; 
lean_del_object(v___x_214_);
v___x_218_ = l_Lean_Meta_AbstractNestedProofs_getLambdaBody(v_e_203_);
lean_dec_ref(v_e_203_);
v_dummy_219_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_220_ = l_Lean_Expr_getAppNumArgs(v___x_218_);
lean_inc(v_nargs_220_);
v___x_221_ = lean_mk_array(v_nargs_220_, v_dummy_219_);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_sub(v_nargs_220_, v___x_222_);
lean_dec(v_nargs_220_);
v___x_224_ = lean_unbox(v_a_211_);
lean_dec(v_a_211_);
v___x_225_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v___x_224_, v___x_217_, v_env_204_, v___x_218_, v___x_221_, v___x_223_);
return v___x_225_;
}
else
{
uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
lean_dec(v_a_211_);
lean_dec_ref(v_env_204_);
lean_dec_ref(v_e_203_);
v___x_226_ = 0;
v___x_227_ = lean_box(v___x_226_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_227_);
v___x_229_ = v___x_214_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_204_);
lean_dec_ref(v_e_203_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed(lean_object* v_e_233_, lean_object* v_env_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(v_e_233_, v_env_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
return v_res_240_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_241_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg(){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__1);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v___dummy_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg();
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(lean_object* v___y_248_, uint8_t v_isExporting_249_, lean_object* v___x_250_, lean_object* v___y_251_, lean_object* v___x_252_, lean_object* v_a_x3f_253_){
_start:
{
lean_object* v___x_255_; lean_object* v_env_256_; lean_object* v_nextMacroScope_257_; lean_object* v_ngen_258_; lean_object* v_auxDeclNGen_259_; lean_object* v_traceState_260_; lean_object* v_recordedDeps_261_; lean_object* v_messages_262_; lean_object* v_infoState_263_; lean_object* v_snapshotTasks_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_289_; 
v___x_255_ = lean_st_ref_take(v___y_248_);
v_env_256_ = lean_ctor_get(v___x_255_, 0);
v_nextMacroScope_257_ = lean_ctor_get(v___x_255_, 1);
v_ngen_258_ = lean_ctor_get(v___x_255_, 2);
v_auxDeclNGen_259_ = lean_ctor_get(v___x_255_, 3);
v_traceState_260_ = lean_ctor_get(v___x_255_, 4);
v_recordedDeps_261_ = lean_ctor_get(v___x_255_, 6);
v_messages_262_ = lean_ctor_get(v___x_255_, 7);
v_infoState_263_ = lean_ctor_get(v___x_255_, 8);
v_snapshotTasks_264_ = lean_ctor_get(v___x_255_, 9);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v___x_255_, 5);
lean_dec(v_unused_290_);
v___x_266_ = v___x_255_;
v_isShared_267_ = v_isSharedCheck_289_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_snapshotTasks_264_);
lean_inc(v_infoState_263_);
lean_inc(v_messages_262_);
lean_inc(v_recordedDeps_261_);
lean_inc(v_traceState_260_);
lean_inc(v_auxDeclNGen_259_);
lean_inc(v_ngen_258_);
lean_inc(v_nextMacroScope_257_);
lean_inc(v_env_256_);
lean_dec(v___x_255_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_289_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_268_ = l_Lean_Environment_setExporting(v_env_256_, v_isExporting_249_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 5, v___x_250_);
lean_ctor_set(v___x_266_, 0, v___x_268_);
v___x_270_ = v___x_266_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_nextMacroScope_257_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_ngen_258_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_auxDeclNGen_259_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v_traceState_260_);
lean_ctor_set(v_reuseFailAlloc_288_, 5, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_288_, 6, v_recordedDeps_261_);
lean_ctor_set(v_reuseFailAlloc_288_, 7, v_messages_262_);
lean_ctor_set(v_reuseFailAlloc_288_, 8, v_infoState_263_);
lean_ctor_set(v_reuseFailAlloc_288_, 9, v_snapshotTasks_264_);
v___x_270_ = v_reuseFailAlloc_288_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v_mctx_273_; lean_object* v_zetaDeltaFVarIds_274_; lean_object* v_postponed_275_; lean_object* v_diag_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_286_; 
v___x_271_ = lean_st_ref_put(v___y_248_, v___x_270_);
v___x_272_ = lean_st_ref_take(v___y_251_);
v_mctx_273_ = lean_ctor_get(v___x_272_, 0);
v_zetaDeltaFVarIds_274_ = lean_ctor_get(v___x_272_, 2);
v_postponed_275_ = lean_ctor_get(v___x_272_, 3);
v_diag_276_ = lean_ctor_get(v___x_272_, 4);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v___x_272_, 1);
lean_dec(v_unused_287_);
v___x_278_ = v___x_272_;
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_diag_276_);
lean_inc(v_postponed_275_);
lean_inc(v_zetaDeltaFVarIds_274_);
lean_inc(v_mctx_273_);
lean_dec(v___x_272_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_box(0);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v___x_252_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_mctx_273_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_zetaDeltaFVarIds_274_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v_postponed_275_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v_diag_276_);
v___x_282_ = v_reuseFailAlloc_285_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_st_ref_put(v___y_251_, v___x_282_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_280_);
return v___x_284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_291_, lean_object* v_isExporting_292_, lean_object* v___x_293_, lean_object* v___y_294_, lean_object* v___x_295_, lean_object* v_a_x3f_296_, lean_object* v___y_297_){
_start:
{
uint8_t v_isExporting_boxed_298_; lean_object* v_res_299_; 
v_isExporting_boxed_298_ = lean_unbox(v_isExporting_292_);
v_res_299_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_291_, v_isExporting_boxed_298_, v___x_293_, v___y_294_, v___x_295_, v_a_x3f_296_);
lean_dec(v_a_x3f_296_);
lean_dec(v___y_294_);
lean_dec(v___y_291_);
return v_res_299_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4___redArg();
return v___x_304_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0);
v___x_309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
lean_ctor_set(v___x_309_, 2, v___x_307_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_310_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__4, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__4);
v___x_311_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
v___x_312_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0);
v___x_313_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
v___x_314_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___x_312_);
lean_ctor_set(v___x_314_, 2, v___x_311_);
lean_ctor_set(v___x_314_, 3, v___x_312_);
lean_ctor_set(v___x_314_, 4, v___x_312_);
lean_ctor_set(v___x_314_, 5, v___x_312_);
lean_ctor_set(v___x_314_, 6, v___x_312_);
lean_ctor_set(v___x_314_, 7, v___x_310_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(lean_object* v_x_315_, uint8_t v_isExporting_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v___x_322_; lean_object* v_env_323_; lean_object* v___x_324_; uint8_t v_isModule_325_; 
v___x_322_ = lean_st_ref_get(v___y_320_);
v_env_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc_ref(v_env_323_);
lean_dec(v___x_322_);
v___x_324_ = l_Lean_Environment_header(v_env_323_);
v_isModule_325_ = lean_ctor_get_uint8(v___x_324_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_324_);
if (v_isModule_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec_ref(v_env_323_);
lean_inc(v___y_320_);
lean_inc_ref(v___y_319_);
lean_inc(v___y_318_);
lean_inc_ref(v___y_317_);
v___x_326_ = lean_apply_5(v_x_315_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, lean_box(0));
return v___x_326_;
}
else
{
uint8_t v_isExporting_327_; 
v_isExporting_327_ = lean_ctor_get_uint8(v_env_323_, sizeof(void*)*13);
lean_dec_ref(v_env_323_);
if (v_isExporting_316_ == 0)
{
if (v_isExporting_327_ == 0)
{
lean_object* v___x_394_; 
lean_inc(v___y_320_);
lean_inc_ref(v___y_319_);
lean_inc(v___y_318_);
lean_inc_ref(v___y_317_);
v___x_394_ = lean_apply_5(v_x_315_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, lean_box(0));
return v___x_394_;
}
else
{
goto v___jp_328_;
}
}
else
{
if (v_isExporting_327_ == 0)
{
goto v___jp_328_;
}
else
{
lean_object* v___x_395_; 
lean_inc(v___y_320_);
lean_inc_ref(v___y_319_);
lean_inc(v___y_318_);
lean_inc_ref(v___y_317_);
v___x_395_ = lean_apply_5(v_x_315_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, lean_box(0));
return v___x_395_;
}
}
v___jp_328_:
{
lean_object* v___x_329_; lean_object* v_env_330_; lean_object* v_nextMacroScope_331_; lean_object* v_ngen_332_; lean_object* v_auxDeclNGen_333_; lean_object* v_traceState_334_; lean_object* v_recordedDeps_335_; lean_object* v_messages_336_; lean_object* v_infoState_337_; lean_object* v_snapshotTasks_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_392_; 
v___x_329_ = lean_st_ref_take(v___y_320_);
v_env_330_ = lean_ctor_get(v___x_329_, 0);
v_nextMacroScope_331_ = lean_ctor_get(v___x_329_, 1);
v_ngen_332_ = lean_ctor_get(v___x_329_, 2);
v_auxDeclNGen_333_ = lean_ctor_get(v___x_329_, 3);
v_traceState_334_ = lean_ctor_get(v___x_329_, 4);
v_recordedDeps_335_ = lean_ctor_get(v___x_329_, 6);
v_messages_336_ = lean_ctor_get(v___x_329_, 7);
v_infoState_337_ = lean_ctor_get(v___x_329_, 8);
v_snapshotTasks_338_ = lean_ctor_get(v___x_329_, 9);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; 
v_unused_393_ = lean_ctor_get(v___x_329_, 5);
lean_dec(v_unused_393_);
v___x_340_ = v___x_329_;
v_isShared_341_ = v_isSharedCheck_392_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_snapshotTasks_338_);
lean_inc(v_infoState_337_);
lean_inc(v_messages_336_);
lean_inc(v_recordedDeps_335_);
lean_inc(v_traceState_334_);
lean_inc(v_auxDeclNGen_333_);
lean_inc(v_ngen_332_);
lean_inc(v_nextMacroScope_331_);
lean_inc(v_env_330_);
lean_dec(v___x_329_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_392_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_342_ = l_Lean_Environment_setExporting(v_env_330_, v_isExporting_316_);
v___x_343_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 5, v___x_343_);
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_345_ = v___x_340_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_nextMacroScope_331_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_ngen_332_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v_auxDeclNGen_333_);
lean_ctor_set(v_reuseFailAlloc_391_, 4, v_traceState_334_);
lean_ctor_set(v_reuseFailAlloc_391_, 5, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_391_, 6, v_recordedDeps_335_);
lean_ctor_set(v_reuseFailAlloc_391_, 7, v_messages_336_);
lean_ctor_set(v_reuseFailAlloc_391_, 8, v_infoState_337_);
lean_ctor_set(v_reuseFailAlloc_391_, 9, v_snapshotTasks_338_);
v___x_345_ = v_reuseFailAlloc_391_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_mctx_348_; lean_object* v_zetaDeltaFVarIds_349_; lean_object* v_postponed_350_; lean_object* v_diag_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_389_; 
v___x_346_ = lean_st_ref_put(v___y_320_, v___x_345_);
v___x_347_ = lean_st_ref_take(v___y_318_);
v_mctx_348_ = lean_ctor_get(v___x_347_, 0);
v_zetaDeltaFVarIds_349_ = lean_ctor_get(v___x_347_, 2);
v_postponed_350_ = lean_ctor_get(v___x_347_, 3);
v_diag_351_ = lean_ctor_get(v___x_347_, 4);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; 
v_unused_390_ = lean_ctor_get(v___x_347_, 1);
lean_dec(v_unused_390_);
v___x_353_ = v___x_347_;
v_isShared_354_ = v_isSharedCheck_389_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_diag_351_);
lean_inc(v_postponed_350_);
lean_inc(v_zetaDeltaFVarIds_349_);
lean_inc(v_mctx_348_);
lean_dec(v___x_347_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_389_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_355_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__5, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__5);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_355_);
v___x_357_ = v___x_353_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_mctx_348_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_zetaDeltaFVarIds_349_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v_postponed_350_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v_diag_351_);
v___x_357_ = v_reuseFailAlloc_388_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v_r_359_; 
v___x_358_ = lean_st_ref_put(v___y_318_, v___x_357_);
lean_inc(v___y_320_);
lean_inc_ref(v___y_319_);
lean_inc(v___y_318_);
lean_inc_ref(v___y_317_);
v_r_359_ = lean_apply_5(v_x_315_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, lean_box(0));
if (lean_obj_tag(v_r_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_376_; 
v_a_360_ = lean_ctor_get(v_r_359_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v_r_359_);
if (v_isSharedCheck_376_ == 0)
{
v___x_362_ = v_r_359_;
v_isShared_363_ = v_isSharedCheck_376_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v_r_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_376_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
lean_inc(v_a_360_);
if (v_isShared_363_ == 0)
{
lean_ctor_set_tag(v___x_362_, 1);
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_375_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v___x_366_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_320_, v_isExporting_327_, v___x_343_, v___y_318_, v___x_355_, v___x_365_);
lean_dec_ref(v___x_365_);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v___x_366_, 0);
lean_dec(v_unused_374_);
v___x_368_ = v___x_366_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_dec(v___x_366_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v_a_360_);
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_360_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
v_a_377_ = lean_ctor_get(v_r_359_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v_r_359_, 1);
v___x_378_ = lean_box(0);
v___x_379_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_320_, v_isExporting_327_, v___x_343_, v___y_318_, v___x_355_, v___x_378_);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; 
v_unused_387_ = lean_ctor_get(v___x_379_, 0);
lean_dec(v_unused_387_);
v___x_381_ = v___x_379_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_dec(v___x_379_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set_tag(v___x_381_, 1);
lean_ctor_set(v___x_381_, 0, v_a_377_);
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_377_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___boxed(lean_object* v_x_396_, lean_object* v_isExporting_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
uint8_t v_isExporting_boxed_403_; lean_object* v_res_404_; 
v_isExporting_boxed_403_ = lean_unbox(v_isExporting_397_);
v_res_404_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_396_, v_isExporting_boxed_403_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object* v_x_405_, uint8_t v_when_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
if (v_when_406_ == 0)
{
lean_object* v___x_412_; 
lean_inc(v___y_410_);
lean_inc_ref(v___y_409_);
lean_inc(v___y_408_);
lean_inc_ref(v___y_407_);
v___x_412_ = lean_apply_5(v_x_405_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, lean_box(0));
return v___x_412_;
}
else
{
uint8_t v___x_413_; lean_object* v___x_414_; 
v___x_413_ = 0;
v___x_414_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_405_, v___x_413_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object* v_x_415_, lean_object* v_when_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
uint8_t v_when_boxed_422_; lean_object* v_res_423_; 
v_when_boxed_422_ = lean_unbox(v_when_416_);
v_res_423_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_415_, v_when_boxed_422_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object* v_e_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_430_; lean_object* v_env_431_; lean_object* v___f_432_; uint8_t v___x_433_; lean_object* v___x_434_; 
v___x_430_ = lean_st_ref_get(v_a_428_);
v_env_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc_ref(v_env_431_);
lean_dec(v___x_430_);
v___f_432_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed), 7, 2);
lean_closure_set(v___f_432_, 0, v_e_424_);
lean_closure_set(v___f_432_, 1, v_env_431_);
v___x_433_ = 1;
v___x_434_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v___f_432_, v___x_433_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object* v_e_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(uint8_t v_a_442_, uint8_t v___x_443_, lean_object* v___x_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_a_442_, v___x_443_, v___x_444_, v_x_445_, v_x_446_, v_x_447_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object* v_a_454_, lean_object* v___x_455_, lean_object* v___x_456_, lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
uint8_t v_a_5009__boxed_465_; uint8_t v___x_5010__boxed_466_; lean_object* v_res_467_; 
v_a_5009__boxed_465_ = lean_unbox(v_a_454_);
v___x_5010__boxed_466_ = lean_unbox(v___x_455_);
v_res_467_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(v_a_5009__boxed_465_, v___x_5010__boxed_466_, v___x_456_, v_x_457_, v_x_458_, v_x_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object* v_00_u03b1_468_, lean_object* v_x_469_, uint8_t v_when_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_469_, v_when_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object* v_00_u03b1_477_, lean_object* v_x_478_, lean_object* v_when_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
uint8_t v_when_boxed_485_; lean_object* v_res_486_; 
v_when_boxed_485_ = lean_unbox(v_when_479_);
v_res_486_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(v_00_u03b1_477_, v_x_478_, v_when_boxed_485_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(lean_object* v_00_u03b1_487_, lean_object* v_x_488_, uint8_t v_isExporting_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_488_, v_isExporting_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___boxed(lean_object* v_00_u03b1_496_, lean_object* v_x_497_, lean_object* v_isExporting_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
uint8_t v_isExporting_boxed_504_; lean_object* v_res_505_; 
v_isExporting_boxed_504_ = lean_unbox(v_isExporting_498_);
v_res_505_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(v_00_u03b1_496_, v_x_497_, v_isExporting_boxed_504_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3___redArg(){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v___dummy_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3___redArg();
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(lean_object* v_x_514_, uint8_t v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_box(v___y_515_);
lean_inc(v___y_516_);
v___x_523_ = lean_apply_7(v_x_514_, v___x_522_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, lean_box(0));
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed(lean_object* v_x_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v___y_27392__boxed_532_; lean_object* v_res_533_; 
v___y_27392__boxed_532_ = lean_unbox(v___y_525_);
v_res_533_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(v_x_524_, v___y_27392__boxed_532_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_526_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object* v_lctx_534_, lean_object* v_localInsts_535_, lean_object* v_x_536_, uint8_t v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; lean_object* v___f_545_; lean_object* v___x_546_; 
v___x_544_ = lean_box(v___y_537_);
lean_inc(v___y_538_);
v___f_545_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_545_, 0, v_x_536_);
lean_closure_set(v___f_545_, 1, v___x_544_);
lean_closure_set(v___f_545_, 2, v___y_538_);
v___x_546_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_534_, v_localInsts_535_, v___f_545_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
if (lean_obj_tag(v___x_546_) == 0)
{
return v___x_546_;
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___boxed(lean_object* v_lctx_555_, lean_object* v_localInsts_556_, lean_object* v_x_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
uint8_t v___y_27417__boxed_565_; lean_object* v_res_566_; 
v___y_27417__boxed_565_ = lean_unbox(v___y_558_);
v_res_566_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_lctx_555_, v_localInsts_556_, v_x_557_, v___y_27417__boxed_565_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object* v_00_u03b1_567_, lean_object* v_lctx_568_, lean_object* v_localInsts_569_, lean_object* v_x_570_, uint8_t v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_lctx_568_, v_localInsts_569_, v_x_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object* v_00_u03b1_579_, lean_object* v_lctx_580_, lean_object* v_localInsts_581_, lean_object* v_x_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
uint8_t v___y_27461__boxed_590_; lean_object* v_res_591_; 
v___y_27461__boxed_590_ = lean_unbox(v___y_583_);
v_res_591_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_00_u03b1_579_, v_lctx_580_, v_localInsts_581_, v_x_582_, v___y_27461__boxed_590_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(lean_object* v_k_592_, uint8_t v___y_593_, lean_object* v___y_594_, lean_object* v_b_595_, lean_object* v_c_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_box(v___y_593_);
lean_inc(v___y_600_);
lean_inc_ref(v___y_599_);
lean_inc(v___y_598_);
lean_inc_ref(v___y_597_);
lean_inc(v___y_594_);
v___x_603_ = lean_apply_9(v_k_592_, v_b_595_, v_c_596_, v___x_602_, v___y_594_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, lean_box(0));
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed(lean_object* v_k_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v_b_607_, lean_object* v_c_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
uint8_t v___y_27484__boxed_614_; lean_object* v_res_615_; 
v___y_27484__boxed_614_ = lean_unbox(v___y_605_);
v_res_615_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(v_k_604_, v___y_27484__boxed_614_, v___y_606_, v_b_607_, v_c_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_606_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(lean_object* v_e_616_, lean_object* v_k_617_, uint8_t v_cleanupAnnotations_618_, uint8_t v_preserveNondepLet_619_, uint8_t v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; lean_object* v___f_628_; uint8_t v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_627_ = lean_box(v___y_620_);
lean_inc(v___y_621_);
v___f_628_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_628_, 0, v_k_617_);
lean_closure_set(v___f_628_, 1, v___x_627_);
lean_closure_set(v___f_628_, 2, v___y_621_);
v___x_629_ = 1;
v___x_630_ = 0;
v___x_631_ = lean_box(0);
v___x_632_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_616_, v___x_629_, v___x_629_, v_preserveNondepLet_619_, v___x_630_, v___x_631_, v___f_628_, v_cleanupAnnotations_618_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_632_) == 0)
{
return v___x_632_;
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___boxed(lean_object* v_e_641_, lean_object* v_k_642_, lean_object* v_cleanupAnnotations_643_, lean_object* v_preserveNondepLet_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_652_; uint8_t v_preserveNondepLet_boxed_653_; uint8_t v___y_27509__boxed_654_; lean_object* v_res_655_; 
v_cleanupAnnotations_boxed_652_ = lean_unbox(v_cleanupAnnotations_643_);
v_preserveNondepLet_boxed_653_ = lean_unbox(v_preserveNondepLet_644_);
v___y_27509__boxed_654_ = lean_unbox(v___y_645_);
v_res_655_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_e_641_, v_k_642_, v_cleanupAnnotations_boxed_652_, v_preserveNondepLet_boxed_653_, v___y_27509__boxed_654_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object* v_00_u03b1_656_, lean_object* v_e_657_, lean_object* v_k_658_, uint8_t v_cleanupAnnotations_659_, uint8_t v_preserveNondepLet_660_, uint8_t v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_e_657_, v_k_658_, v_cleanupAnnotations_659_, v_preserveNondepLet_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object* v_00_u03b1_669_, lean_object* v_e_670_, lean_object* v_k_671_, lean_object* v_cleanupAnnotations_672_, lean_object* v_preserveNondepLet_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_681_; uint8_t v_preserveNondepLet_boxed_682_; uint8_t v___y_27559__boxed_683_; lean_object* v_res_684_; 
v_cleanupAnnotations_boxed_681_ = lean_unbox(v_cleanupAnnotations_672_);
v_preserveNondepLet_boxed_682_ = lean_unbox(v_preserveNondepLet_673_);
v___y_27559__boxed_683_ = lean_unbox(v___y_674_);
v_res_684_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_00_u03b1_669_, v_e_670_, v_k_671_, v_cleanupAnnotations_boxed_681_, v_preserveNondepLet_boxed_682_, v___y_27559__boxed_683_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object* v_type_685_, lean_object* v_k_686_, uint8_t v_cleanupAnnotations_687_, uint8_t v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; lean_object* v___f_696_; uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_695_ = lean_box(v___y_688_);
lean_inc(v___y_689_);
v___f_696_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_696_, 0, v_k_686_);
lean_closure_set(v___f_696_, 1, v___x_695_);
lean_closure_set(v___f_696_, 2, v___y_689_);
v___x_697_ = 0;
v___x_698_ = lean_box(0);
v___x_699_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_697_, v___x_698_, v_type_685_, v___f_696_, v_cleanupAnnotations_687_, v___x_697_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_699_) == 0)
{
return v___x_699_;
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object* v_type_708_, lean_object* v_k_709_, lean_object* v_cleanupAnnotations_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_718_; uint8_t v___y_27582__boxed_719_; lean_object* v_res_720_; 
v_cleanupAnnotations_boxed_718_ = lean_unbox(v_cleanupAnnotations_710_);
v___y_27582__boxed_719_ = lean_unbox(v___y_711_);
v_res_720_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_type_708_, v_k_709_, v_cleanupAnnotations_boxed_718_, v___y_27582__boxed_719_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object* v_00_u03b1_721_, lean_object* v_type_722_, lean_object* v_k_723_, uint8_t v_cleanupAnnotations_724_, uint8_t v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_type_722_, v_k_723_, v_cleanupAnnotations_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object* v_00_u03b1_733_, lean_object* v_type_734_, lean_object* v_k_735_, lean_object* v_cleanupAnnotations_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_744_; uint8_t v___y_27630__boxed_745_; lean_object* v_res_746_; 
v_cleanupAnnotations_boxed_744_ = lean_unbox(v_cleanupAnnotations_736_);
v___y_27630__boxed_745_ = lean_unbox(v___y_737_);
v_res_746_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(v_00_u03b1_733_, v_type_734_, v_k_735_, v_cleanupAnnotations_boxed_744_, v___y_27630__boxed_745_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
lean_object* v_ks_751_; lean_object* v_vs_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_776_; 
v_ks_751_ = lean_ctor_get(v_x_747_, 0);
v_vs_752_ = lean_ctor_get(v_x_747_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_776_ == 0)
{
v___x_754_ = v_x_747_;
v_isShared_755_ = v_isSharedCheck_776_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_vs_752_);
lean_inc(v_ks_751_);
lean_dec(v_x_747_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_776_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = lean_array_get_size(v_ks_751_);
v___x_757_ = lean_nat_dec_lt(v_x_748_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
lean_dec(v_x_748_);
v___x_758_ = lean_array_push(v_ks_751_, v_x_749_);
v___x_759_ = lean_array_push(v_vs_752_, v_x_750_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v___x_759_);
lean_ctor_set(v___x_754_, 0, v___x_758_);
v___x_761_ = v___x_754_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
else
{
lean_object* v_k_x27_763_; uint8_t v___x_764_; 
v_k_x27_763_ = lean_array_fget_borrowed(v_ks_751_, v_x_748_);
v___x_764_ = l_Lean_instBEqFVarId_beq(v_x_749_, v_k_x27_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_766_; 
if (v_isShared_755_ == 0)
{
v___x_766_ = v___x_754_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_ks_751_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_vs_752_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = lean_nat_add(v_x_748_, v___x_767_);
lean_dec(v_x_748_);
v_x_747_ = v___x_766_;
v_x_748_ = v___x_768_;
goto _start;
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_771_ = lean_array_fset(v_ks_751_, v_x_748_, v_x_749_);
v___x_772_ = lean_array_fset(v_vs_752_, v_x_748_, v_x_750_);
lean_dec(v_x_748_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v___x_772_);
lean_ctor_set(v___x_754_, 0, v___x_771_);
v___x_774_ = v___x_754_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(lean_object* v_n_777_, lean_object* v_k_778_, lean_object* v_v_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(v_n_777_, v___x_780_, v_k_778_, v_v_779_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object* v_x_783_, size_t v_x_784_, size_t v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
lean_object* v_es_788_; size_t v___x_789_; size_t v___x_790_; lean_object* v_j_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_es_788_ = lean_ctor_get(v_x_783_, 0);
v___x_789_ = ((size_t)31ULL);
v___x_790_ = lean_usize_land(v_x_784_, v___x_789_);
v_j_791_ = lean_usize_to_nat(v___x_790_);
v___x_792_ = lean_array_get_size(v_es_788_);
v___x_793_ = lean_nat_dec_lt(v_j_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_dec(v_j_791_);
lean_dec(v_x_787_);
lean_dec(v_x_786_);
return v_x_783_;
}
else
{
lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_832_; 
lean_inc_ref(v_es_788_);
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_783_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v_x_783_, 0);
lean_dec(v_unused_833_);
v___x_795_ = v_x_783_;
v_isShared_796_ = v_isSharedCheck_832_;
goto v_resetjp_794_;
}
else
{
lean_dec(v_x_783_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_832_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_v_797_; lean_object* v___x_798_; lean_object* v_xs_x27_799_; lean_object* v___y_801_; 
v_v_797_ = lean_array_fget(v_es_788_, v_j_791_);
v___x_798_ = lean_box(0);
v_xs_x27_799_ = lean_array_fset(v_es_788_, v_j_791_, v___x_798_);
switch(lean_obj_tag(v_v_797_))
{
case 0:
{
lean_object* v_key_806_; lean_object* v_val_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_817_; 
v_key_806_ = lean_ctor_get(v_v_797_, 0);
v_val_807_ = lean_ctor_get(v_v_797_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_v_797_);
if (v_isSharedCheck_817_ == 0)
{
v___x_809_ = v_v_797_;
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_val_807_);
lean_inc(v_key_806_);
lean_dec(v_v_797_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
uint8_t v___x_811_; 
v___x_811_ = l_Lean_instBEqFVarId_beq(v_x_786_, v_key_806_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; 
lean_del_object(v___x_809_);
v___x_812_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_806_, v_val_807_, v_x_786_, v_x_787_);
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
v___y_801_ = v___x_813_;
goto v___jp_800_;
}
else
{
lean_object* v___x_815_; 
lean_dec(v_val_807_);
lean_dec(v_key_806_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 1, v_x_787_);
lean_ctor_set(v___x_809_, 0, v_x_786_);
v___x_815_ = v___x_809_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_x_786_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_x_787_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
v___y_801_ = v___x_815_;
goto v___jp_800_;
}
}
}
}
case 1:
{
lean_object* v_node_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_830_; 
v_node_818_ = lean_ctor_get(v_v_797_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v_v_797_);
if (v_isSharedCheck_830_ == 0)
{
v___x_820_ = v_v_797_;
v_isShared_821_ = v_isSharedCheck_830_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_node_818_);
lean_dec(v_v_797_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_830_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
size_t v___x_822_; size_t v___x_823_; size_t v___x_824_; size_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_822_ = ((size_t)5ULL);
v___x_823_ = lean_usize_shift_right(v_x_784_, v___x_822_);
v___x_824_ = ((size_t)1ULL);
v___x_825_ = lean_usize_add(v_x_785_, v___x_824_);
v___x_826_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_node_818_, v___x_823_, v___x_825_, v_x_786_, v_x_787_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_826_);
v___x_828_ = v___x_820_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v___y_801_ = v___x_828_;
goto v___jp_800_;
}
}
}
default: 
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_x_786_);
lean_ctor_set(v___x_831_, 1, v_x_787_);
v___y_801_ = v___x_831_;
goto v___jp_800_;
}
}
v___jp_800_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_array_fset(v_xs_x27_799_, v_j_791_, v___y_801_);
lean_dec(v_j_791_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_802_);
v___x_804_ = v___x_795_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
else
{
lean_object* v_ks_834_; lean_object* v_vs_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_853_; 
v_ks_834_ = lean_ctor_get(v_x_783_, 0);
v_vs_835_ = lean_ctor_get(v_x_783_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_x_783_);
if (v_isSharedCheck_853_ == 0)
{
v___x_837_ = v_x_783_;
v_isShared_838_ = v_isSharedCheck_853_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_vs_835_);
lean_inc(v_ks_834_);
lean_dec(v_x_783_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_853_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_ks_834_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_vs_835_);
v___x_840_ = v_reuseFailAlloc_852_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v_newNode_841_; size_t v___x_842_; uint8_t v___x_843_; 
v_newNode_841_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(v___x_840_, v_x_786_, v_x_787_);
v___x_842_ = ((size_t)7ULL);
v___x_843_ = lean_usize_dec_le(v___x_842_, v_x_785_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_844_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_841_);
v___x_845_ = lean_unsigned_to_nat(4u);
v___x_846_ = lean_nat_dec_lt(v___x_844_, v___x_845_);
lean_dec(v___x_844_);
if (v___x_846_ == 0)
{
lean_object* v_ks_847_; lean_object* v_vs_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_ks_847_ = lean_ctor_get(v_newNode_841_, 0);
lean_inc_ref(v_ks_847_);
v_vs_848_ = lean_ctor_get(v_newNode_841_, 1);
lean_inc_ref(v_vs_848_);
lean_dec_ref(v_newNode_841_);
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0);
v___x_851_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_x_785_, v_ks_847_, v_vs_848_, v___x_849_, v___x_850_);
lean_dec_ref(v_vs_848_);
lean_dec_ref(v_ks_847_);
return v___x_851_;
}
else
{
return v_newNode_841_;
}
}
else
{
return v_newNode_841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(size_t v_depth_854_, lean_object* v_keys_855_, lean_object* v_vals_856_, lean_object* v_i_857_, lean_object* v_entries_858_){
_start:
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = lean_array_get_size(v_keys_855_);
v___x_860_ = lean_nat_dec_lt(v_i_857_, v___x_859_);
if (v___x_860_ == 0)
{
lean_dec(v_i_857_);
return v_entries_858_;
}
else
{
lean_object* v_k_861_; lean_object* v_v_862_; uint64_t v___x_863_; size_t v_h_864_; size_t v___x_865_; lean_object* v___x_866_; size_t v___x_867_; size_t v___x_868_; size_t v___x_869_; size_t v_h_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_k_861_ = lean_array_fget_borrowed(v_keys_855_, v_i_857_);
v_v_862_ = lean_array_fget_borrowed(v_vals_856_, v_i_857_);
v___x_863_ = l_Lean_instHashableFVarId_hash(v_k_861_);
v_h_864_ = lean_uint64_to_usize(v___x_863_);
v___x_865_ = ((size_t)5ULL);
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = ((size_t)1ULL);
v___x_868_ = lean_usize_sub(v_depth_854_, v___x_867_);
v___x_869_ = lean_usize_mul(v___x_865_, v___x_868_);
v_h_870_ = lean_usize_shift_right(v_h_864_, v___x_869_);
v___x_871_ = lean_nat_add(v_i_857_, v___x_866_);
lean_dec(v_i_857_);
lean_inc(v_v_862_);
lean_inc(v_k_861_);
v___x_872_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_entries_858_, v_h_870_, v_depth_854_, v_k_861_, v_v_862_);
v_i_857_ = v___x_871_;
v_entries_858_ = v___x_872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_depth_874_, lean_object* v_keys_875_, lean_object* v_vals_876_, lean_object* v_i_877_, lean_object* v_entries_878_){
_start:
{
size_t v_depth_boxed_879_; lean_object* v_res_880_; 
v_depth_boxed_879_ = lean_unbox_usize(v_depth_874_);
lean_dec(v_depth_874_);
v_res_880_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_depth_boxed_879_, v_keys_875_, v_vals_876_, v_i_877_, v_entries_878_);
lean_dec_ref(v_vals_876_);
lean_dec_ref(v_keys_875_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
size_t v_x_27730__boxed_886_; size_t v_x_27731__boxed_887_; lean_object* v_res_888_; 
v_x_27730__boxed_886_ = lean_unbox_usize(v_x_882_);
lean_dec(v_x_882_);
v_x_27731__boxed_887_ = lean_unbox_usize(v_x_883_);
lean_dec(v_x_883_);
v_res_888_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_881_, v_x_27730__boxed_886_, v_x_27731__boxed_887_, v_x_884_, v_x_885_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object* v_x_889_, lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
uint64_t v___x_892_; size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; 
v___x_892_ = l_Lean_instHashableFVarId_hash(v_x_890_);
v___x_893_ = lean_uint64_to_usize(v___x_892_);
v___x_894_ = ((size_t)1ULL);
v___x_895_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_889_, v___x_893_, v___x_894_, v_x_890_, v_x_891_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(lean_object* v_a_896_, lean_object* v_b_897_, lean_object* v_x_898_){
_start:
{
if (lean_obj_tag(v_x_898_) == 0)
{
lean_dec(v_b_897_);
lean_dec_ref(v_a_896_);
return v_x_898_;
}
else
{
lean_object* v_key_899_; lean_object* v_value_900_; lean_object* v_tail_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_913_; 
v_key_899_ = lean_ctor_get(v_x_898_, 0);
v_value_900_ = lean_ctor_get(v_x_898_, 1);
v_tail_901_ = lean_ctor_get(v_x_898_, 2);
v_isSharedCheck_913_ = !lean_is_exclusive(v_x_898_);
if (v_isSharedCheck_913_ == 0)
{
v___x_903_ = v_x_898_;
v_isShared_904_ = v_isSharedCheck_913_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_tail_901_);
lean_inc(v_value_900_);
lean_inc(v_key_899_);
lean_dec(v_x_898_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_913_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
uint8_t v___x_905_; 
v___x_905_ = l_Lean_ExprStructEq_beq(v_key_899_, v_a_896_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_896_, v_b_897_, v_tail_901_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 2, v___x_906_);
v___x_908_ = v___x_903_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_key_899_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_value_900_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
else
{
lean_object* v___x_911_; 
lean_dec(v_value_900_);
lean_dec(v_key_899_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v_b_897_);
lean_ctor_set(v___x_903_, 0, v_a_896_);
v___x_911_ = v___x_903_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_896_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_b_897_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_tail_901_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(lean_object* v_a_914_, lean_object* v_x_915_){
_start:
{
if (lean_obj_tag(v_x_915_) == 0)
{
uint8_t v___x_916_; 
v___x_916_ = 0;
return v___x_916_;
}
else
{
lean_object* v_key_917_; lean_object* v_tail_918_; uint8_t v___x_919_; 
v_key_917_ = lean_ctor_get(v_x_915_, 0);
v_tail_918_ = lean_ctor_get(v_x_915_, 2);
v___x_919_ = l_Lean_ExprStructEq_beq(v_key_917_, v_a_914_);
if (v___x_919_ == 0)
{
v_x_915_ = v_tail_918_;
goto _start;
}
else
{
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg___boxed(lean_object* v_a_921_, lean_object* v_x_922_){
_start:
{
uint8_t v_res_923_; lean_object* v_r_924_; 
v_res_923_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_921_, v_x_922_);
lean_dec(v_x_922_);
lean_dec_ref(v_a_921_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
if (lean_obj_tag(v_x_926_) == 0)
{
return v_x_925_;
}
else
{
lean_object* v_key_927_; lean_object* v_value_928_; lean_object* v_tail_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_952_; 
v_key_927_ = lean_ctor_get(v_x_926_, 0);
v_value_928_ = lean_ctor_get(v_x_926_, 1);
v_tail_929_ = lean_ctor_get(v_x_926_, 2);
v_isSharedCheck_952_ = !lean_is_exclusive(v_x_926_);
if (v_isSharedCheck_952_ == 0)
{
v___x_931_ = v_x_926_;
v_isShared_932_ = v_isSharedCheck_952_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_tail_929_);
lean_inc(v_value_928_);
lean_inc(v_key_927_);
lean_dec(v_x_926_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_952_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; uint64_t v___x_936_; uint64_t v_fold_937_; uint64_t v___x_938_; uint64_t v___x_939_; uint64_t v___x_940_; size_t v___x_941_; size_t v___x_942_; size_t v___x_943_; size_t v___x_944_; size_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_933_ = lean_array_get_size(v_x_925_);
v___x_934_ = l_Lean_ExprStructEq_hash(v_key_927_);
v___x_935_ = 32ULL;
v___x_936_ = lean_uint64_shift_right(v___x_934_, v___x_935_);
v_fold_937_ = lean_uint64_xor(v___x_934_, v___x_936_);
v___x_938_ = 16ULL;
v___x_939_ = lean_uint64_shift_right(v_fold_937_, v___x_938_);
v___x_940_ = lean_uint64_xor(v_fold_937_, v___x_939_);
v___x_941_ = lean_uint64_to_usize(v___x_940_);
v___x_942_ = lean_usize_of_nat(v___x_933_);
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_sub(v___x_942_, v___x_943_);
v___x_945_ = lean_usize_land(v___x_941_, v___x_944_);
v___x_946_ = lean_array_uget_borrowed(v_x_925_, v___x_945_);
lean_inc(v___x_946_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 2, v___x_946_);
v___x_948_ = v___x_931_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_key_927_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_value_928_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v___x_946_);
v___x_948_ = v_reuseFailAlloc_951_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; 
v___x_949_ = lean_array_uset(v_x_925_, v___x_945_, v___x_948_);
v_x_925_ = v___x_949_;
v_x_926_ = v_tail_929_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(lean_object* v_i_953_, lean_object* v_source_954_, lean_object* v_target_955_){
_start:
{
lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_956_ = lean_array_get_size(v_source_954_);
v___x_957_ = lean_nat_dec_lt(v_i_953_, v___x_956_);
if (v___x_957_ == 0)
{
lean_dec_ref(v_source_954_);
lean_dec(v_i_953_);
return v_target_955_;
}
else
{
lean_object* v_es_958_; lean_object* v___x_959_; lean_object* v_source_960_; lean_object* v_target_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_es_958_ = lean_array_fget(v_source_954_, v_i_953_);
v___x_959_ = lean_box(0);
v_source_960_ = lean_array_fset(v_source_954_, v_i_953_, v___x_959_);
v_target_961_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(v_target_955_, v_es_958_);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_add(v_i_953_, v___x_962_);
lean_dec(v_i_953_);
v_i_953_ = v___x_963_;
v_source_954_ = v_source_960_;
v_target_955_ = v_target_961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(lean_object* v_data_965_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_nbuckets_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_966_ = lean_array_get_size(v_data_965_);
v___x_967_ = lean_unsigned_to_nat(2u);
v_nbuckets_968_ = lean_nat_mul(v___x_966_, v___x_967_);
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = lean_box(0);
v___x_971_ = lean_mk_array(v_nbuckets_968_, v___x_970_);
v___x_972_ = lean_array_propagate_mark(v_data_965_, v___x_971_);
v___x_973_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(v___x_969_, v_data_965_, v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(lean_object* v_m_974_, lean_object* v_a_975_, lean_object* v_b_976_){
_start:
{
lean_object* v_size_977_; lean_object* v_buckets_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1021_; 
v_size_977_ = lean_ctor_get(v_m_974_, 0);
v_buckets_978_ = lean_ctor_get(v_m_974_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_m_974_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_980_ = v_m_974_;
v_isShared_981_ = v_isSharedCheck_1021_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_buckets_978_);
lean_inc(v_size_977_);
lean_dec(v_m_974_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1021_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; uint64_t v___x_983_; uint64_t v___x_984_; uint64_t v___x_985_; uint64_t v_fold_986_; uint64_t v___x_987_; uint64_t v___x_988_; uint64_t v___x_989_; size_t v___x_990_; size_t v___x_991_; size_t v___x_992_; size_t v___x_993_; size_t v___x_994_; lean_object* v_bkt_995_; uint8_t v___x_996_; 
v___x_982_ = lean_array_get_size(v_buckets_978_);
v___x_983_ = l_Lean_ExprStructEq_hash(v_a_975_);
v___x_984_ = 32ULL;
v___x_985_ = lean_uint64_shift_right(v___x_983_, v___x_984_);
v_fold_986_ = lean_uint64_xor(v___x_983_, v___x_985_);
v___x_987_ = 16ULL;
v___x_988_ = lean_uint64_shift_right(v_fold_986_, v___x_987_);
v___x_989_ = lean_uint64_xor(v_fold_986_, v___x_988_);
v___x_990_ = lean_uint64_to_usize(v___x_989_);
v___x_991_ = lean_usize_of_nat(v___x_982_);
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_sub(v___x_991_, v___x_992_);
v___x_994_ = lean_usize_land(v___x_990_, v___x_993_);
v_bkt_995_ = lean_array_uget_borrowed(v_buckets_978_, v___x_994_);
v___x_996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_975_, v_bkt_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v_size_x27_998_; lean_object* v___x_999_; lean_object* v_buckets_x27_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_997_ = lean_unsigned_to_nat(1u);
v_size_x27_998_ = lean_nat_add(v_size_977_, v___x_997_);
lean_dec(v_size_977_);
lean_inc(v_bkt_995_);
v___x_999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_999_, 0, v_a_975_);
lean_ctor_set(v___x_999_, 1, v_b_976_);
lean_ctor_set(v___x_999_, 2, v_bkt_995_);
v_buckets_x27_1000_ = lean_array_uset(v_buckets_978_, v___x_994_, v___x_999_);
v___x_1001_ = lean_unsigned_to_nat(4u);
v___x_1002_ = lean_nat_mul(v_size_x27_998_, v___x_1001_);
v___x_1003_ = lean_unsigned_to_nat(3u);
v___x_1004_ = lean_nat_div(v___x_1002_, v___x_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_array_get_size(v_buckets_x27_1000_);
v___x_1006_ = lean_nat_dec_le(v___x_1004_, v___x_1005_);
lean_dec(v___x_1004_);
if (v___x_1006_ == 0)
{
lean_object* v_val_1007_; lean_object* v___x_1009_; 
v_val_1007_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(v_buckets_x27_1000_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v_val_1007_);
lean_ctor_set(v___x_980_, 0, v_size_x27_998_);
v___x_1009_ = v___x_980_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_size_x27_998_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_val_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
else
{
lean_object* v___x_1012_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v_buckets_x27_1000_);
lean_ctor_set(v___x_980_, 0, v_size_x27_998_);
v___x_1012_ = v___x_980_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_size_x27_998_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_buckets_x27_1000_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
lean_object* v___x_1014_; lean_object* v_buckets_x27_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
lean_inc(v_bkt_995_);
v___x_1014_ = lean_box(0);
v_buckets_x27_1015_ = lean_array_uset(v_buckets_978_, v___x_994_, v___x_1014_);
v___x_1016_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_975_, v_b_976_, v_bkt_995_);
v___x_1017_ = lean_array_uset(v_buckets_x27_1015_, v___x_994_, v___x_1016_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v___x_1017_);
v___x_1019_ = v___x_980_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_size_977_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(lean_object* v_a_1022_, lean_object* v_x_1023_){
_start:
{
if (lean_obj_tag(v_x_1023_) == 0)
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_box(0);
return v___x_1024_;
}
else
{
lean_object* v_key_1025_; lean_object* v_value_1026_; lean_object* v_tail_1027_; uint8_t v___x_1028_; 
v_key_1025_ = lean_ctor_get(v_x_1023_, 0);
v_value_1026_ = lean_ctor_get(v_x_1023_, 1);
v_tail_1027_ = lean_ctor_get(v_x_1023_, 2);
v___x_1028_ = l_Lean_ExprStructEq_beq(v_key_1025_, v_a_1022_);
if (v___x_1028_ == 0)
{
v_x_1023_ = v_tail_1027_;
goto _start;
}
else
{
lean_object* v___x_1030_; 
lean_inc(v_value_1026_);
v___x_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1030_, 0, v_value_1026_);
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___boxed(lean_object* v_a_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1031_, v_x_1032_);
lean_dec(v_x_1032_);
lean_dec_ref(v_a_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(lean_object* v_m_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_buckets_1036_; lean_object* v___x_1037_; uint64_t v___x_1038_; uint64_t v___x_1039_; uint64_t v___x_1040_; uint64_t v_fold_1041_; uint64_t v___x_1042_; uint64_t v___x_1043_; uint64_t v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_buckets_1036_ = lean_ctor_get(v_m_1034_, 1);
v___x_1037_ = lean_array_get_size(v_buckets_1036_);
v___x_1038_ = l_Lean_ExprStructEq_hash(v_a_1035_);
v___x_1039_ = 32ULL;
v___x_1040_ = lean_uint64_shift_right(v___x_1038_, v___x_1039_);
v_fold_1041_ = lean_uint64_xor(v___x_1038_, v___x_1040_);
v___x_1042_ = 16ULL;
v___x_1043_ = lean_uint64_shift_right(v_fold_1041_, v___x_1042_);
v___x_1044_ = lean_uint64_xor(v_fold_1041_, v___x_1043_);
v___x_1045_ = lean_uint64_to_usize(v___x_1044_);
v___x_1046_ = lean_usize_of_nat(v___x_1037_);
v___x_1047_ = ((size_t)1ULL);
v___x_1048_ = lean_usize_sub(v___x_1046_, v___x_1047_);
v___x_1049_ = lean_usize_land(v___x_1045_, v___x_1048_);
v___x_1050_ = lean_array_uget_borrowed(v_buckets_1036_, v___x_1049_);
v___x_1051_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1035_, v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___boxed(lean_object* v_m_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_m_1052_, v_a_1053_);
lean_dec_ref(v_a_1053_);
lean_dec_ref(v_m_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(lean_object* v_x_1055_, uint8_t v_isExporting_1056_, uint8_t v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; lean_object* v_env_1065_; lean_object* v___x_1066_; uint8_t v_isModule_1067_; 
v___x_1064_ = lean_st_ref_get(v___y_1062_);
v_env_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc_ref(v_env_1065_);
lean_dec(v___x_1064_);
v___x_1066_ = l_Lean_Environment_header(v_env_1065_);
v_isModule_1067_ = lean_ctor_get_uint8(v___x_1066_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1066_);
if (v_isModule_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_dec_ref(v_env_1065_);
v___x_1068_ = lean_box(v___y_1057_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
v___x_1069_ = lean_apply_7(v_x_1055_, v___x_1068_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, lean_box(0));
return v___x_1069_;
}
else
{
uint8_t v_isExporting_1070_; 
v_isExporting_1070_ = lean_ctor_get_uint8(v_env_1065_, sizeof(void*)*13);
lean_dec_ref(v_env_1065_);
if (v_isExporting_1056_ == 0)
{
if (v_isExporting_1070_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_box(v___y_1057_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
v___x_1139_ = lean_apply_7(v_x_1055_, v___x_1138_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, lean_box(0));
return v___x_1139_;
}
else
{
goto v___jp_1071_;
}
}
else
{
if (v_isExporting_1070_ == 0)
{
goto v___jp_1071_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_box(v___y_1057_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
v___x_1141_ = lean_apply_7(v_x_1055_, v___x_1140_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, lean_box(0));
return v___x_1141_;
}
}
v___jp_1071_:
{
lean_object* v___x_1072_; lean_object* v_env_1073_; lean_object* v_nextMacroScope_1074_; lean_object* v_ngen_1075_; lean_object* v_auxDeclNGen_1076_; lean_object* v_traceState_1077_; lean_object* v_recordedDeps_1078_; lean_object* v_messages_1079_; lean_object* v_infoState_1080_; lean_object* v_snapshotTasks_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1136_; 
v___x_1072_ = lean_st_ref_take(v___y_1062_);
v_env_1073_ = lean_ctor_get(v___x_1072_, 0);
v_nextMacroScope_1074_ = lean_ctor_get(v___x_1072_, 1);
v_ngen_1075_ = lean_ctor_get(v___x_1072_, 2);
v_auxDeclNGen_1076_ = lean_ctor_get(v___x_1072_, 3);
v_traceState_1077_ = lean_ctor_get(v___x_1072_, 4);
v_recordedDeps_1078_ = lean_ctor_get(v___x_1072_, 6);
v_messages_1079_ = lean_ctor_get(v___x_1072_, 7);
v_infoState_1080_ = lean_ctor_get(v___x_1072_, 8);
v_snapshotTasks_1081_ = lean_ctor_get(v___x_1072_, 9);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v___x_1072_, 5);
lean_dec(v_unused_1137_);
v___x_1083_ = v___x_1072_;
v_isShared_1084_ = v_isSharedCheck_1136_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_snapshotTasks_1081_);
lean_inc(v_infoState_1080_);
lean_inc(v_messages_1079_);
lean_inc(v_recordedDeps_1078_);
lean_inc(v_traceState_1077_);
lean_inc(v_auxDeclNGen_1076_);
lean_inc(v_ngen_1075_);
lean_inc(v_nextMacroScope_1074_);
lean_inc(v_env_1073_);
lean_dec(v___x_1072_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1136_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1085_ = l_Lean_Environment_setExporting(v_env_1073_, v_isExporting_1056_);
v___x_1086_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 5, v___x_1086_);
lean_ctor_set(v___x_1083_, 0, v___x_1085_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_nextMacroScope_1074_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_ngen_1075_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_auxDeclNGen_1076_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_traceState_1077_);
lean_ctor_set(v_reuseFailAlloc_1135_, 5, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1135_, 6, v_recordedDeps_1078_);
lean_ctor_set(v_reuseFailAlloc_1135_, 7, v_messages_1079_);
lean_ctor_set(v_reuseFailAlloc_1135_, 8, v_infoState_1080_);
lean_ctor_set(v_reuseFailAlloc_1135_, 9, v_snapshotTasks_1081_);
v___x_1088_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_mctx_1091_; lean_object* v_zetaDeltaFVarIds_1092_; lean_object* v_postponed_1093_; lean_object* v_diag_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1133_; 
v___x_1089_ = lean_st_ref_put(v___y_1062_, v___x_1088_);
v___x_1090_ = lean_st_ref_take(v___y_1060_);
v_mctx_1091_ = lean_ctor_get(v___x_1090_, 0);
v_zetaDeltaFVarIds_1092_ = lean_ctor_get(v___x_1090_, 2);
v_postponed_1093_ = lean_ctor_get(v___x_1090_, 3);
v_diag_1094_ = lean_ctor_get(v___x_1090_, 4);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v___x_1090_, 1);
lean_dec(v_unused_1134_);
v___x_1096_ = v___x_1090_;
v_isShared_1097_ = v_isSharedCheck_1133_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_diag_1094_);
lean_inc(v_postponed_1093_);
lean_inc(v_zetaDeltaFVarIds_1092_);
lean_inc(v_mctx_1091_);
lean_dec(v___x_1090_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1133_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__5, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__5);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v___x_1098_);
v___x_1100_ = v___x_1096_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_mctx_1091_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_zetaDeltaFVarIds_1092_);
lean_ctor_set(v_reuseFailAlloc_1132_, 3, v_postponed_1093_);
lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_diag_1094_);
v___x_1100_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v_r_1103_; 
v___x_1101_ = lean_st_ref_put(v___y_1060_, v___x_1100_);
v___x_1102_ = lean_box(v___y_1057_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
v_r_1103_ = lean_apply_7(v_x_1055_, v___x_1102_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, lean_box(0));
if (lean_obj_tag(v_r_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1120_; 
v_a_1104_ = lean_ctor_get(v_r_1103_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_r_1103_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1106_ = v_r_1103_;
v_isShared_1107_ = v_isSharedCheck_1120_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v_r_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1120_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
lean_inc(v_a_1104_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 1);
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v___x_1110_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_1062_, v_isExporting_1070_, v___x_1086_, v___y_1060_, v___x_1098_, v___x_1109_);
lean_dec_ref(v___x_1109_);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v___x_1110_, 0);
lean_dec(v_unused_1118_);
v___x_1112_ = v___x_1110_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_dec(v___x_1110_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v_a_1104_);
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1104_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_a_1121_ = lean_ctor_get(v_r_1103_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v_r_1103_, 1);
v___x_1122_ = lean_box(0);
v___x_1123_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_1062_, v_isExporting_1070_, v___x_1086_, v___y_1060_, v___x_1098_, v___x_1122_);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v___x_1123_, 0);
lean_dec(v_unused_1131_);
v___x_1125_ = v___x_1123_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_dec(v___x_1123_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 1);
lean_ctor_set(v___x_1125_, 0, v_a_1121_);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1121_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg___boxed(lean_object* v_x_1142_, lean_object* v_isExporting_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
uint8_t v_isExporting_boxed_1151_; uint8_t v___y_28172__boxed_1152_; lean_object* v_res_1153_; 
v_isExporting_boxed_1151_ = lean_unbox(v_isExporting_1143_);
v___y_28172__boxed_1152_ = lean_unbox(v___y_1144_);
v_res_1153_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(v_x_1142_, v_isExporting_boxed_1151_, v___y_28172__boxed_1152_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(lean_object* v_x_1154_, uint8_t v_when_1155_, uint8_t v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
if (v_when_1155_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_box(v___y_1156_);
lean_inc(v___y_1161_);
lean_inc_ref(v___y_1160_);
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
lean_inc(v___y_1157_);
v___x_1164_ = lean_apply_7(v_x_1154_, v___x_1163_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, lean_box(0));
return v___x_1164_;
}
else
{
uint8_t v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = 0;
v___x_1166_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(v_x_1154_, v___x_1165_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg___boxed(lean_object* v_x_1167_, lean_object* v_when_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
uint8_t v_when_boxed_1176_; uint8_t v___y_28325__boxed_1177_; lean_object* v_res_1178_; 
v_when_boxed_1176_ = lean_unbox(v_when_1168_);
v___y_28325__boxed_1177_ = lean_unbox(v___y_1169_);
v_res_1178_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(v_x_1167_, v_when_boxed_1176_, v___y_28325__boxed_1177_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0(lean_object* v_proof_1179_, uint8_t v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; 
lean_inc(v___y_1185_);
lean_inc_ref(v___y_1184_);
lean_inc(v___y_1183_);
lean_inc_ref(v___y_1182_);
v___x_1187_ = lean_infer_type(v_proof_1179_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0___boxed(lean_object* v_proof_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v___y_28354__boxed_1196_; lean_object* v_res_1197_; 
v___y_28354__boxed_1196_ = lean_unbox(v___y_1189_);
v_res_1197_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0(v_proof_1188_, v___y_28354__boxed_1196_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object* v_proof_1198_, uint8_t v_cache_1199_, lean_object* v_postprocessType_1200_, uint8_t v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___f_1208_; uint8_t v___x_1209_; lean_object* v___x_1210_; 
lean_inc_ref(v_proof_1198_);
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1208_, 0, v_proof_1198_);
v___x_1209_ = 1;
v___x_1210_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(v___f_1208_, v___x_1209_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = l_Lean_Core_betaReduce(v_a_1211_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v___x_1214_ = l_Lean_Meta_zetaReduce(v_a_1213_, v___x_1209_, v___x_1209_, v___x_1209_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = lean_box(v___y_1201_);
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1205_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1203_);
lean_inc(v___y_1202_);
v___x_1217_ = lean_apply_8(v_postprocessType_1200_, v_a_1215_, v___x_1216_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, lean_box(0));
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; uint8_t v___y_1220_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
if (v_cache_1199_ == 0)
{
v___y_1220_ = v_cache_1199_;
goto v___jp_1219_;
}
else
{
uint8_t v___x_1223_; 
v___x_1223_ = l_Lean_Expr_hasSorry(v_proof_1198_);
if (v___x_1223_ == 0)
{
v___y_1220_ = v_cache_1199_;
goto v___jp_1219_;
}
else
{
uint8_t v___x_1224_; 
v___x_1224_ = 0;
v___y_1220_ = v___x_1224_;
goto v___jp_1219_;
}
}
v___jp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = l_Lean_Meta_mkAuxTheorem(v_a_1218_, v_proof_1198_, v___x_1209_, v___x_1221_, v___y_1220_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
return v___x_1222_;
}
}
else
{
lean_dec_ref(v_proof_1198_);
return v___x_1217_;
}
}
else
{
lean_dec_ref(v_postprocessType_1200_);
lean_dec_ref(v_proof_1198_);
return v___x_1214_;
}
}
else
{
lean_dec_ref(v_postprocessType_1200_);
lean_dec_ref(v_proof_1198_);
return v___x_1212_;
}
}
else
{
lean_dec_ref(v_postprocessType_1200_);
lean_dec_ref(v_proof_1198_);
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object* v_proof_1225_, lean_object* v_cache_1226_, lean_object* v_postprocessType_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
uint8_t v_cache_boxed_1235_; uint8_t v___y_28377__boxed_1236_; lean_object* v_res_1237_; 
v_cache_boxed_1235_ = lean_unbox(v_cache_1226_);
v___y_28377__boxed_1236_ = lean_unbox(v___y_1228_);
v_res_1237_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_proof_1225_, v_cache_boxed_1235_, v_postprocessType_1227_, v___y_28377__boxed_1236_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object* v_as_1238_, size_t v_sz_1239_, size_t v_i_1240_, lean_object* v_b_1241_, uint8_t v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_a_1250_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; uint8_t v___x_1263_; 
v___x_1263_ = lean_usize_dec_lt(v_i_1240_, v_sz_1239_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_b_1241_);
return v___x_1264_;
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1266_; lean_object* v_localDecl_1268_; lean_object* v___x_1276_; 
v_a_1265_ = lean_array_uget_borrowed(v_as_1238_, v_i_1240_);
v___x_1266_ = l_Lean_Expr_fvarId_x21(v_a_1265_);
lean_inc(v___x_1266_);
v___x_1276_ = l_Lean_FVarId_getDecl___redArg(v___x_1266_, v___y_1244_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1278_ = l_Lean_LocalDecl_type(v_a_1277_);
v___x_1279_ = l_Lean_Meta_AbstractNestedProofs_visit(v___x_1278_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = l_Lean_LocalDecl_setType(v_a_1277_, v_a_1280_);
v___x_1282_ = l_Lean_LocalDecl_value_x3f(v___x_1281_, v___x_1263_);
if (lean_obj_tag(v___x_1282_) == 0)
{
v_localDecl_1268_ = v___x_1281_;
goto v___jp_1267_;
}
else
{
lean_object* v_val_1283_; lean_object* v___x_1284_; 
v_val_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_val_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v___x_1284_ = l_Lean_Meta_AbstractNestedProofs_visit(v_val_1283_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1286_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = l_Lean_LocalDecl_setValue(v___x_1281_, v_a_1285_);
v_localDecl_1268_ = v___x_1286_;
goto v___jp_1267_;
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v___x_1281_);
lean_dec(v___x_1266_);
lean_dec_ref(v_b_1241_);
v_a_1287_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1284_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1284_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_a_1277_);
lean_dec(v___x_1266_);
lean_dec_ref(v_b_1241_);
v_a_1295_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1279_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1279_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v___x_1266_);
lean_dec_ref(v_b_1241_);
v_a_1303_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1276_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1276_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
v___jp_1267_:
{
lean_object* v_fvarIdToDecl_1269_; lean_object* v_decls_1270_; lean_object* v_auxDeclToFullName_1271_; lean_object* v___x_1272_; 
v_fvarIdToDecl_1269_ = lean_ctor_get(v_b_1241_, 0);
v_decls_1270_ = lean_ctor_get(v_b_1241_, 1);
v_auxDeclToFullName_1271_ = lean_ctor_get(v_b_1241_, 2);
lean_inc_ref(v_b_1241_);
v___x_1272_ = lean_local_ctx_find(v_b_1241_, v___x_1266_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_dec_ref(v_localDecl_1268_);
v_a_1250_ = v_b_1241_;
goto v___jp_1249_;
}
else
{
lean_object* v_index_1273_; lean_object* v_fvarId_1274_; lean_object* v___x_1275_; 
lean_inc(v_auxDeclToFullName_1271_);
lean_inc_ref(v_decls_1270_);
lean_inc_ref(v_fvarIdToDecl_1269_);
lean_dec_ref_known(v___x_1272_, 1);
lean_dec_ref(v_b_1241_);
v_index_1273_ = lean_ctor_get(v_localDecl_1268_, 0);
lean_inc(v_index_1273_);
v_fvarId_1274_ = lean_ctor_get(v_localDecl_1268_, 1);
lean_inc_ref(v_localDecl_1268_);
lean_inc(v_fvarId_1274_);
v___x_1275_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_fvarIdToDecl_1269_, v_fvarId_1274_, v_localDecl_1268_);
v___y_1255_ = v_localDecl_1268_;
v___y_1256_ = v_decls_1270_;
v___y_1257_ = v___x_1275_;
v___y_1258_ = v_auxDeclToFullName_1271_;
v___y_1259_ = v_index_1273_;
goto v___jp_1254_;
}
}
}
v___jp_1249_:
{
size_t v___x_1251_; size_t v___x_1252_; 
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = lean_usize_add(v_i_1240_, v___x_1251_);
v_i_1240_ = v___x_1252_;
v_b_1241_ = v_a_1250_;
goto _start;
}
v___jp_1254_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___y_1255_);
v___x_1261_ = l_Lean_PersistentArray_set___redArg(v___y_1256_, v___y_1259_, v___x_1260_);
lean_dec(v___y_1259_);
v___x_1262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1262_, 0, v___y_1257_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
lean_ctor_set(v___x_1262_, 2, v___y_1258_);
v_a_1250_ = v___x_1262_;
goto v___jp_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object* v_xs_1311_, lean_object* v_k_1312_, uint8_t v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_lctx_1320_; lean_object* v_localInstances_1321_; size_t v_sz_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v_lctx_1320_ = lean_ctor_get(v___y_1315_, 2);
v_localInstances_1321_ = lean_ctor_get(v___y_1315_, 3);
v_sz_1322_ = lean_array_size(v_xs_1311_);
v___x_1323_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1320_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_xs_1311_, v_sz_1322_, v___x_1323_, v_lctx_1320_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1326_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
lean_inc_ref(v_localInstances_1321_);
v___x_1326_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_a_1325_, v_localInstances_1321_, v_k_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
return v___x_1326_;
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_k_1312_);
v_a_1327_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1324_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1324_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object* v_xs_1335_, lean_object* v_k_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
uint8_t v___y_28488__boxed_1344_; lean_object* v_res_1345_; 
v___y_28488__boxed_1344_ = lean_unbox(v___y_1337_);
v_res_1345_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(v_xs_1335_, v_k_1336_, v___y_28488__boxed_1344_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v_xs_1335_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object* v___y_1347_, lean_object* v___f_1348_, lean_object* v_xs_1349_, lean_object* v_b_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v___y_28438__boxed_1358_; uint8_t v___y_28440__boxed_1359_; lean_object* v_res_1360_; 
v___y_28438__boxed_1358_ = lean_unbox(v___y_1347_);
v___y_28440__boxed_1359_ = lean_unbox(v___y_1351_);
v_res_1360_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(v___y_28438__boxed_1358_, v___f_1348_, v_xs_1349_, v_b_1350_, v___y_28440__boxed_1359_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object* v_b_1361_, lean_object* v_xs_1362_, uint8_t v___y_1363_, uint8_t v___x_1364_, uint8_t v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1361_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = 1;
v___x_1375_ = l_Lean_Meta_mkForallFVars(v_xs_1362_, v_a_1373_, v___y_1363_, v___x_1364_, v___x_1364_, v___x_1374_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
return v___x_1375_;
}
else
{
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object* v_b_1376_, lean_object* v_xs_1377_, lean_object* v___y_1378_, lean_object* v___x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v___y_28474__boxed_1387_; uint8_t v___x_28475__boxed_1388_; uint8_t v___y_28476__boxed_1389_; lean_object* v_res_1390_; 
v___y_28474__boxed_1387_ = lean_unbox(v___y_1378_);
v___x_28475__boxed_1388_ = lean_unbox(v___x_1379_);
v___y_28476__boxed_1389_ = lean_unbox(v___y_1380_);
v_res_1390_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(v_b_1376_, v_xs_1377_, v___y_28474__boxed_1387_, v___x_28475__boxed_1388_, v___y_28476__boxed_1389_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v_xs_1377_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t v___y_1391_, uint8_t v___x_1392_, lean_object* v___f_1393_, lean_object* v_xs_1394_, lean_object* v_b_1395_, uint8_t v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___f_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1403_ = lean_box(v___y_1391_);
v___x_1404_ = lean_box(v___x_1392_);
lean_inc_ref(v_xs_1394_);
v___f_1405_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1405_, 0, v_b_1395_);
lean_closure_set(v___f_1405_, 1, v_xs_1394_);
lean_closure_set(v___f_1405_, 2, v___x_1403_);
lean_closure_set(v___f_1405_, 3, v___x_1404_);
v___x_1406_ = lean_box(v___y_1396_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v___y_1399_);
lean_inc_ref(v___y_1398_);
lean_inc(v___y_1397_);
v___x_1407_ = lean_apply_9(v___f_1393_, v_xs_1394_, v___f_1405_, v___x_1406_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, lean_box(0));
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object* v___y_1408_, lean_object* v___x_1409_, lean_object* v___f_1410_, lean_object* v_xs_1411_, lean_object* v_b_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
uint8_t v___y_28449__boxed_1420_; uint8_t v___x_28450__boxed_1421_; uint8_t v___y_28452__boxed_1422_; lean_object* v_res_1423_; 
v___y_28449__boxed_1420_ = lean_unbox(v___y_1408_);
v___x_28450__boxed_1421_ = lean_unbox(v___x_1409_);
v___y_28452__boxed_1422_ = lean_unbox(v___y_1413_);
v_res_1423_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(v___y_28449__boxed_1420_, v___x_28450__boxed_1421_, v___f_1410_, v_xs_1411_, v_b_1412_, v___y_28452__boxed_1422_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t v_sz_1424_, size_t v_i_1425_, lean_object* v_bs_1426_, uint8_t v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
uint8_t v___x_1434_; 
v___x_1434_ = lean_usize_dec_lt(v_i_1425_, v_sz_1424_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v_bs_1426_);
return v___x_1435_;
}
else
{
lean_object* v_v_1436_; lean_object* v___x_1437_; lean_object* v_bs_x27_1438_; lean_object* v___x_1439_; 
v_v_1436_ = lean_array_uget(v_bs_1426_, v_i_1425_);
v___x_1437_ = lean_unsigned_to_nat(0u);
v_bs_x27_1438_ = lean_array_uset(v_bs_1426_, v_i_1425_, v___x_1437_);
v___x_1439_ = l_Lean_Meta_AbstractNestedProofs_visit(v_v_1436_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; size_t v___x_1441_; size_t v___x_1442_; lean_object* v___x_1443_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1441_ = ((size_t)1ULL);
v___x_1442_ = lean_usize_add(v_i_1425_, v___x_1441_);
v___x_1443_ = lean_array_uset(v_bs_x27_1438_, v_i_1425_, v_a_1440_);
v_i_1425_ = v___x_1442_;
v_bs_1426_ = v___x_1443_;
goto _start;
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v_bs_x27_1438_);
v_a_1445_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1439_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1439_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v_x_1455_, uint8_t v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
if (lean_obj_tag(v_x_1453_) == 5)
{
lean_object* v_fn_1463_; lean_object* v_arg_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v_fn_1463_ = lean_ctor_get(v_x_1453_, 0);
lean_inc_ref(v_fn_1463_);
v_arg_1464_ = lean_ctor_get(v_x_1453_, 1);
lean_inc_ref(v_arg_1464_);
lean_dec_ref_known(v_x_1453_, 2);
v___x_1465_ = lean_array_set(v_x_1454_, v_x_1455_, v_arg_1464_);
v___x_1466_ = lean_unsigned_to_nat(1u);
v___x_1467_ = lean_nat_sub(v_x_1455_, v___x_1466_);
lean_dec(v_x_1455_);
v_x_1453_ = v_fn_1463_;
v_x_1454_ = v___x_1465_;
v_x_1455_ = v___x_1467_;
goto _start;
}
else
{
lean_object* v___x_1469_; 
lean_dec(v_x_1455_);
v___x_1469_ = l_Lean_Meta_AbstractNestedProofs_visit(v_x_1453_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; size_t v_sz_1471_; size_t v___x_1472_; lean_object* v___x_1473_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v_sz_1471_ = lean_array_size(v_x_1454_);
v___x_1472_ = ((size_t)0ULL);
v___x_1473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_1471_, v___x_1472_, v_x_1454_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1482_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1482_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1482_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1478_ = l_Lean_mkAppN(v_a_1470_, v_a_1474_);
lean_dec(v_a_1474_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1478_);
v___x_1480_ = v___x_1476_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_a_1470_);
v_a_1483_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1473_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1473_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_dec_ref(v_x_1454_);
return v___x_1469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object* v_e_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
uint8_t v_a_boxed_1499_; lean_object* v_res_1500_; 
v_a_boxed_1499_ = lean_unbox(v_a_1492_);
v_res_1500_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1491_, v_a_boxed_1499_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object* v_e_1501_, uint8_t v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_a_1510_; lean_object* v___y_1516_; lean_object* v___f_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___f_1518_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed), 9, 0);
v___x_1519_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_visit___closed__0));
v___x_1520_ = l_Lean_Core_checkSystem(v___x_1519_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1584_; 
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; 
v_unused_1585_ = lean_ctor_get(v___x_1520_, 0);
lean_dec(v_unused_1585_);
v___x_1522_ = v___x_1520_;
v_isShared_1523_ = v_isSharedCheck_1584_;
goto v_resetjp_1521_;
}
else
{
lean_dec(v___x_1520_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1584_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
uint8_t v___x_1524_; 
v___x_1524_ = l_Lean_Expr_isAtomic(v_e_1501_);
if (v___x_1524_ == 0)
{
uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1525_ = 1;
v___x_1526_ = lean_st_ref_get(v_a_1503_);
v___x_1527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v___x_1526_, v_e_1501_);
lean_dec(v___x_1526_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v___x_1528_; 
lean_del_object(v___x_1522_);
lean_inc_ref(v_e_1501_);
v___x_1528_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_1501_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; uint8_t v___y_1531_; uint8_t v___x_1565_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1565_ = lean_unbox(v_a_1529_);
lean_dec(v_a_1529_);
if (v___x_1565_ == 0)
{
v___y_1531_ = v___x_1524_;
goto v___jp_1530_;
}
else
{
uint8_t v___x_1566_; 
v___x_1566_ = l_Lean_Expr_hasSorry(v_e_1501_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec_ref(v___f_1518_);
v___x_1567_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___boxed), 8, 0);
lean_inc_ref(v_e_1501_);
v___x_1568_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_e_1501_, v_a_1502_, v___x_1567_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
v___y_1516_ = v___x_1568_;
goto v___jp_1515_;
}
else
{
v___y_1531_ = v___x_1524_;
goto v___jp_1530_;
}
}
v___jp_1530_:
{
switch(lean_obj_tag(v_e_1501_))
{
case 6:
{
lean_object* v___x_1532_; lean_object* v___f_1533_; lean_object* v___x_1534_; 
v___x_1532_ = lean_box(v___y_1531_);
v___f_1533_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1533_, 0, v___x_1532_);
lean_closure_set(v___f_1533_, 1, v___f_1518_);
lean_inc_ref(v_e_1501_);
v___x_1534_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_e_1501_, v___f_1533_, v___y_1531_, v___x_1525_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
v___y_1516_ = v___x_1534_;
goto v___jp_1515_;
}
case 8:
{
lean_object* v___x_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; 
v___x_1535_ = lean_box(v___y_1531_);
v___f_1536_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1536_, 0, v___x_1535_);
lean_closure_set(v___f_1536_, 1, v___f_1518_);
lean_inc_ref(v_e_1501_);
v___x_1537_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_e_1501_, v___f_1536_, v___y_1531_, v___x_1525_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
v___y_1516_ = v___x_1537_;
goto v___jp_1515_;
}
case 7:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___f_1540_; lean_object* v___x_1541_; 
v___x_1538_ = lean_box(v___y_1531_);
v___x_1539_ = lean_box(v___x_1525_);
v___f_1540_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed), 12, 3);
lean_closure_set(v___f_1540_, 0, v___x_1538_);
lean_closure_set(v___f_1540_, 1, v___x_1539_);
lean_closure_set(v___f_1540_, 2, v___f_1518_);
lean_inc_ref(v_e_1501_);
v___x_1541_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1501_, v___f_1540_, v___y_1531_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
v___y_1516_ = v___x_1541_;
goto v___jp_1515_;
}
case 10:
{
lean_object* v_data_1542_; lean_object* v_expr_1543_; lean_object* v___x_1544_; 
lean_dec_ref(v___f_1518_);
v_data_1542_ = lean_ctor_get(v_e_1501_, 0);
v_expr_1543_ = lean_ctor_get(v_e_1501_, 1);
lean_inc_ref(v_expr_1543_);
v___x_1544_ = l_Lean_Meta_AbstractNestedProofs_visit(v_expr_1543_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; size_t v___x_1546_; size_t v___x_1547_; uint8_t v___x_1548_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1546_ = lean_ptr_addr(v_expr_1543_);
v___x_1547_ = lean_ptr_addr(v_a_1545_);
v___x_1548_ = lean_usize_dec_eq(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_inc(v_data_1542_);
v___x_1549_ = l_Lean_Expr_mdata___override(v_data_1542_, v_a_1545_);
v_a_1510_ = v___x_1549_;
goto v___jp_1509_;
}
else
{
lean_dec(v_a_1545_);
lean_inc_ref(v_e_1501_);
v_a_1510_ = v_e_1501_;
goto v___jp_1509_;
}
}
else
{
lean_dec_ref_known(v_e_1501_, 2);
return v___x_1544_;
}
}
case 11:
{
lean_object* v_typeName_1550_; lean_object* v_idx_1551_; lean_object* v_struct_1552_; lean_object* v___x_1553_; 
lean_dec_ref(v___f_1518_);
v_typeName_1550_ = lean_ctor_get(v_e_1501_, 0);
v_idx_1551_ = lean_ctor_get(v_e_1501_, 1);
v_struct_1552_ = lean_ctor_get(v_e_1501_, 2);
lean_inc_ref(v_struct_1552_);
v___x_1553_ = l_Lean_Meta_AbstractNestedProofs_visit(v_struct_1552_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; size_t v___x_1555_; size_t v___x_1556_; uint8_t v___x_1557_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = lean_ptr_addr(v_struct_1552_);
v___x_1556_ = lean_ptr_addr(v_a_1554_);
v___x_1557_ = lean_usize_dec_eq(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
lean_inc(v_idx_1551_);
lean_inc(v_typeName_1550_);
v___x_1558_ = l_Lean_Expr_proj___override(v_typeName_1550_, v_idx_1551_, v_a_1554_);
v_a_1510_ = v___x_1558_;
goto v___jp_1509_;
}
else
{
lean_dec(v_a_1554_);
lean_inc_ref(v_e_1501_);
v_a_1510_ = v_e_1501_;
goto v___jp_1509_;
}
}
else
{
lean_dec_ref_known(v_e_1501_, 3);
return v___x_1553_;
}
}
case 5:
{
lean_object* v_dummy_1559_; lean_object* v_nargs_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v___f_1518_);
v_dummy_1559_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_1560_ = l_Lean_Expr_getAppNumArgs(v_e_1501_);
lean_inc(v_nargs_1560_);
v___x_1561_ = lean_mk_array(v_nargs_1560_, v_dummy_1559_);
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = lean_nat_sub(v_nargs_1560_, v___x_1562_);
lean_dec(v_nargs_1560_);
lean_inc_ref(v_e_1501_);
v___x_1564_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_e_1501_, v___x_1561_, v___x_1563_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
v___y_1516_ = v___x_1564_;
goto v___jp_1515_;
}
default: 
{
lean_dec_ref(v___f_1518_);
lean_inc_ref(v_e_1501_);
v_a_1510_ = v_e_1501_;
goto v___jp_1509_;
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec_ref(v___f_1518_);
lean_dec_ref(v_e_1501_);
v_a_1569_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1528_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1528_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
lean_object* v_val_1577_; lean_object* v___x_1579_; 
lean_dec_ref(v___f_1518_);
lean_dec_ref(v_e_1501_);
v_val_1577_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v___x_1527_, 1);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v_val_1577_);
v___x_1579_ = v___x_1522_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_val_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
else
{
lean_object* v___x_1582_; 
lean_dec_ref(v___f_1518_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v_e_1501_);
v___x_1582_ = v___x_1522_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_e_1501_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v___f_1518_);
lean_dec_ref(v_e_1501_);
v_a_1586_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1520_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1520_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
v___jp_1509_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1511_ = lean_st_ref_take(v_a_1503_);
lean_inc_ref(v_a_1510_);
v___x_1512_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v___x_1511_, v_e_1501_, v_a_1510_);
v___x_1513_ = lean_st_ref_put(v_a_1503_, v___x_1512_);
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_a_1510_);
return v___x_1514_;
}
v___jp_1515_:
{
if (lean_obj_tag(v___y_1516_) == 0)
{
lean_object* v_a_1517_; 
v_a_1517_ = lean_ctor_get(v___y_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___y_1516_, 1);
v_a_1510_ = v_a_1517_;
goto v___jp_1509_;
}
else
{
lean_dec_ref(v_e_1501_);
return v___y_1516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object* v_b_1594_, lean_object* v_xs_1595_, uint8_t v___y_1596_, uint8_t v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1594_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v___x_1606_ = 1;
v___x_1607_ = l_Lean_Meta_mkLambdaFVars(v_xs_1595_, v_a_1605_, v___y_1596_, v___y_1596_, v___y_1596_, v___y_1596_, v___x_1606_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
return v___x_1607_;
}
else
{
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object* v_b_1608_, lean_object* v_xs_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v___y_28461__boxed_1618_; uint8_t v___y_28462__boxed_1619_; lean_object* v_res_1620_; 
v___y_28461__boxed_1618_ = lean_unbox(v___y_1610_);
v___y_28462__boxed_1619_ = lean_unbox(v___y_1611_);
v_res_1620_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(v_b_1608_, v_xs_1609_, v___y_28461__boxed_1618_, v___y_28462__boxed_1619_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v_xs_1609_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t v___y_1621_, lean_object* v___f_1622_, lean_object* v_xs_1623_, lean_object* v_b_1624_, uint8_t v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v___f_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1632_ = lean_box(v___y_1621_);
lean_inc_ref(v_xs_1623_);
v___f_1633_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1633_, 0, v_b_1624_);
lean_closure_set(v___f_1633_, 1, v_xs_1623_);
lean_closure_set(v___f_1633_, 2, v___x_1632_);
v___x_1634_ = lean_box(v___y_1625_);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
lean_inc(v___y_1626_);
v___x_1635_ = lean_apply_9(v___f_1622_, v_xs_1623_, v___f_1633_, v___x_1634_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, lean_box(0));
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object* v_sz_1636_, lean_object* v_i_1637_, lean_object* v_bs_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
size_t v_sz_boxed_1646_; size_t v_i_boxed_1647_; uint8_t v___y_28501__boxed_1648_; lean_object* v_res_1649_; 
v_sz_boxed_1646_ = lean_unbox_usize(v_sz_1636_);
lean_dec(v_sz_1636_);
v_i_boxed_1647_ = lean_unbox_usize(v_i_1637_);
lean_dec(v_i_1637_);
v___y_28501__boxed_1648_ = lean_unbox(v___y_1639_);
v_res_1649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_boxed_1646_, v_i_boxed_1647_, v_bs_1638_, v___y_28501__boxed_1648_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
uint8_t v___y_28522__boxed_1660_; lean_object* v_res_1661_; 
v___y_28522__boxed_1660_ = lean_unbox(v___y_1653_);
v_res_1661_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_x_1650_, v_x_1651_, v_x_1652_, v___y_28522__boxed_1660_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object* v_as_1662_, lean_object* v_sz_1663_, lean_object* v_i_1664_, lean_object* v_b_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
size_t v_sz_boxed_1673_; size_t v_i_boxed_1674_; uint8_t v___y_28545__boxed_1675_; lean_object* v_res_1676_; 
v_sz_boxed_1673_ = lean_unbox_usize(v_sz_1663_);
lean_dec(v_sz_1663_);
v_i_boxed_1674_ = lean_unbox_usize(v_i_1664_);
lean_dec(v_i_1664_);
v___y_28545__boxed_1675_ = lean_unbox(v___y_1666_);
v_res_1676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_as_1662_, v_sz_boxed_1673_, v_i_boxed_1674_, v_b_1665_, v___y_28545__boxed_1675_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v_as_1662_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object* v_00_u03b2_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_x_1678_, v_x_1679_, v_x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object* v_00_u03b2_1682_, lean_object* v_m_1683_, lean_object* v_a_1684_, lean_object* v_b_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_m_1683_, v_a_1684_, v_b_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object* v_00_u03b2_1687_, lean_object* v_m_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_m_1688_, v_a_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object* v_00_u03b2_1691_, lean_object* v_m_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_00_u03b2_1691_, v_m_1692_, v_a_1693_);
lean_dec_ref(v_a_1693_);
lean_dec_ref(v_m_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object* v_00_u03b2_1695_, lean_object* v_x_1696_, size_t v_x_1697_, size_t v_x_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_1696_, v_x_1697_, v_x_1698_, v_x_1699_, v_x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1702_, lean_object* v_x_1703_, lean_object* v_x_1704_, lean_object* v_x_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_){
_start:
{
size_t v_x_29123__boxed_1708_; size_t v_x_29124__boxed_1709_; lean_object* v_res_1710_; 
v_x_29123__boxed_1708_ = lean_unbox_usize(v_x_1704_);
lean_dec(v_x_1704_);
v_x_29124__boxed_1709_ = lean_unbox_usize(v_x_1705_);
lean_dec(v_x_1705_);
v_res_1710_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(v_00_u03b2_1702_, v_x_1703_, v_x_29123__boxed_1708_, v_x_29124__boxed_1709_, v_x_1706_, v_x_1707_);
return v_res_1710_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(lean_object* v_00_u03b2_1711_, lean_object* v_a_1712_, lean_object* v_x_1713_){
_start:
{
uint8_t v___x_1714_; 
v___x_1714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_1712_, v_x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1715_, lean_object* v_a_1716_, lean_object* v_x_1717_){
_start:
{
uint8_t v_res_1718_; lean_object* v_r_1719_; 
v_res_1718_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(v_00_u03b2_1715_, v_a_1716_, v_x_1717_);
lean_dec(v_x_1717_);
lean_dec_ref(v_a_1716_);
v_r_1719_ = lean_box(v_res_1718_);
return v_r_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6(lean_object* v_00_u03b2_1720_, lean_object* v_data_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(v_data_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7(lean_object* v_00_u03b2_1723_, lean_object* v_a_1724_, lean_object* v_b_1725_, lean_object* v_x_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_1724_, v_b_1725_, v_x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(lean_object* v_00_u03b2_1728_, lean_object* v_a_1729_, lean_object* v_x_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1729_, v_x_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1732_, lean_object* v_a_1733_, lean_object* v_x_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(v_00_u03b2_1732_, v_a_1733_, v_x_1734_);
lean_dec(v_x_1734_);
lean_dec_ref(v_a_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14(lean_object* v_00_u03b1_1736_, lean_object* v_x_1737_, uint8_t v_when_1738_, uint8_t v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(v_x_1737_, v_when_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___boxed(lean_object* v_00_u03b1_1747_, lean_object* v_x_1748_, lean_object* v_when_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
uint8_t v_when_boxed_1757_; uint8_t v___y_29155__boxed_1758_; lean_object* v_res_1759_; 
v_when_boxed_1757_ = lean_unbox(v_when_1749_);
v___y_29155__boxed_1758_ = lean_unbox(v___y_1750_);
v_res_1759_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14(v_00_u03b1_1747_, v_x_1748_, v_when_boxed_1757_, v___y_29155__boxed_1758_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_1760_, lean_object* v_n_1761_, lean_object* v_k_1762_, lean_object* v_v_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(v_n_1761_, v_k_1762_, v_v_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_1765_, size_t v_depth_1766_, lean_object* v_keys_1767_, lean_object* v_vals_1768_, lean_object* v_heq_1769_, lean_object* v_i_1770_, lean_object* v_entries_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_depth_1766_, v_keys_1767_, v_vals_1768_, v_i_1770_, v_entries_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_1773_, lean_object* v_depth_1774_, lean_object* v_keys_1775_, lean_object* v_vals_1776_, lean_object* v_heq_1777_, lean_object* v_i_1778_, lean_object* v_entries_1779_){
_start:
{
size_t v_depth_boxed_1780_; lean_object* v_res_1781_; 
v_depth_boxed_1780_ = lean_unbox_usize(v_depth_1774_);
lean_dec(v_depth_1774_);
v_res_1781_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(v_00_u03b2_1773_, v_depth_boxed_1780_, v_keys_1775_, v_vals_1776_, v_heq_1777_, v_i_1778_, v_entries_1779_);
lean_dec_ref(v_vals_1776_);
lean_dec_ref(v_keys_1775_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_1782_, lean_object* v_i_1783_, lean_object* v_source_1784_, lean_object* v_target_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(v_i_1783_, v_source_1784_, v_target_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18(lean_object* v_00_u03b1_1787_, lean_object* v_x_1788_, uint8_t v_isExporting_1789_, uint8_t v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(v_x_1788_, v_isExporting_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1798_, lean_object* v_x_1799_, lean_object* v_isExporting_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
uint8_t v_isExporting_boxed_1808_; uint8_t v___y_29184__boxed_1809_; lean_object* v_res_1810_; 
v_isExporting_boxed_1808_ = lean_unbox(v_isExporting_1800_);
v___y_29184__boxed_1809_ = lean_unbox(v___y_1801_);
v_res_1810_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18(v_00_u03b1_1798_, v_x_1799_, v_isExporting_boxed_1808_, v___y_29184__boxed_1809_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1811_, lean_object* v_x_1812_, lean_object* v_x_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(v_x_1812_, v_x_1813_, v_x_1814_, v_x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16(lean_object* v_00_u03b2_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(v_x_1818_, v_x_1819_);
return v___x_1820_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__0(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = lean_box(0);
v___x_1822_ = lean_unsigned_to_nat(16u);
v___x_1823_ = lean_mk_array(v___x_1822_, v___x_1821_);
return v___x_1823_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__1(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__0, &l_Lean_Meta_abstractNestedProofs___closed__0_once, _init_l_Lean_Meta_abstractNestedProofs___closed__0);
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1824_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs(lean_object* v_e_1827_, uint8_t v_cache_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v___x_1834_; 
lean_inc_ref(v_e_1827_);
v___x_1834_ = l_Lean_Meta_isProof(v_e_1827_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1855_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1855_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1855_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_unbox(v_a_1835_);
lean_dec(v_a_1835_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_del_object(v___x_1837_);
v___x_1840_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__1, &l_Lean_Meta_abstractNestedProofs___closed__1_once, _init_l_Lean_Meta_abstractNestedProofs___closed__1);
v___x_1841_ = lean_st_mk_ref(v___x_1840_);
v___x_1842_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1827_, v_cache_1828_, v___x_1841_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1851_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_st_ref_get(v___x_1841_);
lean_dec(v___x_1841_);
lean_dec(v___x_1847_);
if (v_isShared_1846_ == 0)
{
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1843_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
else
{
lean_dec(v___x_1841_);
return v___x_1842_;
}
}
else
{
lean_object* v___x_1853_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v_e_1827_);
v___x_1853_ = v___x_1837_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_e_1827_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_dec_ref(v_e_1827_);
v_a_1856_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1834_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1834_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object* v_e_1864_, lean_object* v_cache_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
uint8_t v_cache_boxed_1871_; lean_object* v_res_1872_; 
v_cache_boxed_1871_ = lean_unbox(v_cache_1865_);
v_res_1872_ = l_Lean_Meta_abstractNestedProofs(v_e_1864_, v_cache_boxed_1871_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
return v_res_1872_;
}
}
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_AbstractNestedProofs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_AbstractNestedProofs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_AbstractNestedProofs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AbstractNestedProofs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_AbstractNestedProofs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_AbstractNestedProofs(builtin);
}
#ifdef __cplusplus
}
#endif
