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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withoutExporting___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7_spec__12___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__15_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__15___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__16___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "abstract nested proofs"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_visit___closed__0 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__16(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__15_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_abstractNestedProofs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_abstractNestedProofs___closed__0;
static lean_once_cell_t l_Lean_Meta_abstractNestedProofs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_abstractNestedProofs___closed__1;
static lean_once_cell_t l_Lean_Meta_abstractNestedProofs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_abstractNestedProofs___closed__2;
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
uint8_t v___x_150__boxed_20_; uint8_t v_cache_boxed_21_; lean_object* v_res_22_; 
v___x_150__boxed_20_ = lean_unbox(v___x_16_);
v_cache_boxed_21_ = lean_unbox(v_cache_18_);
v_res_22_ = l_Lean_Meta_abstractProof___redArg___lam__0(v_proof_15_, v___x_150__boxed_20_, v_inst_17_, v_cache_boxed_21_, v_type_19_);
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
uint8_t v___x_180__boxed_45_; lean_object* v_res_46_; 
v___x_180__boxed_45_ = lean_unbox(v___x_40_);
v_res_46_ = l_Lean_Meta_abstractProof___redArg___lam__2(v___x_180__boxed_45_, v_inst_41_, v_toBind_42_, v___f_43_, v_type_44_);
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
lean_dec(v_inst_111_);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(uint8_t v_a_123_, uint8_t v___y_124_, lean_object* v_as_125_, size_t v_i_126_, size_t v_stop_127_){
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
v___y_131_ = v___y_124_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0___boxed(lean_object* v_a_138_, lean_object* v___y_139_, lean_object* v_as_140_, lean_object* v_i_141_, lean_object* v_stop_142_){
_start:
{
uint8_t v_a_4312__boxed_143_; uint8_t v___y_4313__boxed_144_; size_t v_i_boxed_145_; size_t v_stop_boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v_a_4312__boxed_143_ = lean_unbox(v_a_138_);
v___y_4313__boxed_144_ = lean_unbox(v___y_139_);
v_i_boxed_145_ = lean_unbox_usize(v_i_141_);
lean_dec(v_i_141_);
v_stop_boxed_146_ = lean_unbox_usize(v_stop_142_);
lean_dec(v_stop_142_);
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_4312__boxed_143_, v___y_4313__boxed_144_, v_as_140_, v_i_boxed_145_, v_stop_boxed_146_);
lean_dec_ref(v_as_140_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(uint8_t v_a_149_, uint8_t v___x_150_, lean_object* v___x_151_, lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
uint8_t v___y_157_; 
if (lean_obj_tag(v_x_152_) == 5)
{
lean_object* v_fn_170_; lean_object* v_arg_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_fn_170_ = lean_ctor_get(v_x_152_, 0);
lean_inc_ref(v_fn_170_);
v_arg_171_ = lean_ctor_get(v_x_152_, 1);
lean_inc_ref(v_arg_171_);
lean_dec_ref_known(v_x_152_, 2);
v___x_172_ = lean_array_set(v_x_153_, v_x_154_, v_arg_171_);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_sub(v_x_154_, v___x_173_);
lean_dec(v_x_154_);
v_x_152_ = v_fn_170_;
v_x_153_ = v___x_172_;
v_x_154_ = v___x_174_;
goto _start;
}
else
{
uint8_t v___x_176_; 
lean_dec(v_x_154_);
v___x_176_ = l_Lean_Expr_isAtomic(v_x_152_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec_ref(v_x_153_);
lean_dec_ref(v_x_152_);
lean_dec_ref(v___x_151_);
v___x_177_ = lean_box(v_a_149_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
else
{
if (v___x_150_ == 0)
{
if (lean_obj_tag(v_x_152_) == 4)
{
lean_object* v_declName_179_; uint8_t v___x_180_; 
v_declName_179_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_declName_179_);
lean_dec_ref_known(v_x_152_, 2);
v___x_180_ = l_Lean_Environment_contains(v___x_151_, v_declName_179_, v_a_149_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec_ref(v_x_153_);
v___x_181_ = lean_box(v_a_149_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
else
{
v___y_157_ = v___x_150_;
goto v___jp_156_;
}
}
else
{
lean_dec_ref(v_x_152_);
lean_dec_ref(v___x_151_);
v___y_157_ = v___x_150_;
goto v___jp_156_;
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec_ref(v_x_153_);
lean_dec_ref(v_x_152_);
lean_dec_ref(v___x_151_);
v___x_183_ = lean_box(v_a_149_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
v___jp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_array_get_size(v_x_153_);
v___x_160_ = lean_nat_dec_lt(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec_ref(v_x_153_);
v___x_161_ = lean_box(v___y_157_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
else
{
if (v___x_160_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec_ref(v_x_153_);
v___x_163_ = lean_box(v___y_157_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
else
{
size_t v___x_165_; size_t v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_165_ = ((size_t)0ULL);
v___x_166_ = lean_usize_of_nat(v___x_159_);
v___x_167_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_149_, v___y_157_, v_x_153_, v___x_165_, v___x_166_);
lean_dec_ref(v_x_153_);
v___x_168_ = lean_box(v___x_167_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg___boxed(lean_object* v_a_185_, lean_object* v___x_186_, lean_object* v___x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v___y_191_){
_start:
{
uint8_t v_a_4338__boxed_192_; uint8_t v___x_4339__boxed_193_; lean_object* v_res_194_; 
v_a_4338__boxed_192_ = lean_unbox(v_a_185_);
v___x_4339__boxed_193_ = lean_unbox(v___x_186_);
v_res_194_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_a_4338__boxed_192_, v___x_4339__boxed_193_, v___x_187_, v_x_188_, v_x_189_, v_x_190_);
return v_res_194_;
}
}
static lean_object* _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4(void){
_start:
{
lean_object* v___x_202_; lean_object* v_dummy_203_; 
v___x_202_ = lean_box(0);
v_dummy_203_ = l_Lean_Expr_sort___override(v___x_202_);
return v_dummy_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(lean_object* v_e_204_, lean_object* v_env_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; 
lean_inc_ref(v_e_204_);
v___x_211_ = l_Lean_Meta_isProof(v_e_204_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; uint8_t v___x_213_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
v___x_213_ = lean_unbox(v_a_212_);
if (v___x_213_ == 0)
{
lean_dec(v_a_212_);
lean_dec_ref(v_env_205_);
lean_dec_ref(v_e_204_);
return v___x_211_;
}
else
{
lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_232_; 
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; 
v_unused_233_ = lean_ctor_get(v___x_211_, 0);
lean_dec(v_unused_233_);
v___x_215_ = v___x_211_;
v_isShared_216_ = v_isSharedCheck_232_;
goto v_resetjp_214_;
}
else
{
lean_dec(v___x_211_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_232_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3));
v___x_218_ = l_Lean_Expr_isAppOf(v_e_204_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v_dummy_220_; lean_object* v_nargs_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; 
lean_del_object(v___x_215_);
v___x_219_ = l_Lean_Meta_AbstractNestedProofs_getLambdaBody(v_e_204_);
lean_dec_ref(v_e_204_);
v_dummy_220_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_221_ = l_Lean_Expr_getAppNumArgs(v___x_219_);
lean_inc(v_nargs_221_);
v___x_222_ = lean_mk_array(v_nargs_221_, v_dummy_220_);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_sub(v_nargs_221_, v___x_223_);
lean_dec(v_nargs_221_);
v___x_225_ = lean_unbox(v_a_212_);
lean_dec(v_a_212_);
v___x_226_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v___x_225_, v___x_218_, v_env_205_, v___x_219_, v___x_222_, v___x_224_);
return v___x_226_;
}
else
{
uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
lean_dec(v_a_212_);
lean_dec_ref(v_env_205_);
lean_dec_ref(v_e_204_);
v___x_227_ = 0;
v___x_228_ = lean_box(v___x_227_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_228_);
v___x_230_ = v___x_215_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_205_);
lean_dec_ref(v_e_204_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed(lean_object* v_e_234_, lean_object* v_env_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(v_e_234_, v_env_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(lean_object* v___y_242_, uint8_t v_isExporting_243_, lean_object* v___x_244_, lean_object* v___y_245_, lean_object* v___x_246_, lean_object* v_a_x3f_247_){
_start:
{
lean_object* v___x_249_; lean_object* v_env_250_; lean_object* v_nextMacroScope_251_; lean_object* v_ngen_252_; lean_object* v_auxDeclNGen_253_; lean_object* v_traceState_254_; lean_object* v_messages_255_; lean_object* v_infoState_256_; lean_object* v_snapshotTasks_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_282_; 
v___x_249_ = lean_st_ref_take(v___y_242_);
v_env_250_ = lean_ctor_get(v___x_249_, 0);
v_nextMacroScope_251_ = lean_ctor_get(v___x_249_, 1);
v_ngen_252_ = lean_ctor_get(v___x_249_, 2);
v_auxDeclNGen_253_ = lean_ctor_get(v___x_249_, 3);
v_traceState_254_ = lean_ctor_get(v___x_249_, 4);
v_messages_255_ = lean_ctor_get(v___x_249_, 6);
v_infoState_256_ = lean_ctor_get(v___x_249_, 7);
v_snapshotTasks_257_ = lean_ctor_get(v___x_249_, 8);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v___x_249_, 5);
lean_dec(v_unused_283_);
v___x_259_ = v___x_249_;
v_isShared_260_ = v_isSharedCheck_282_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_snapshotTasks_257_);
lean_inc(v_infoState_256_);
lean_inc(v_messages_255_);
lean_inc(v_traceState_254_);
lean_inc(v_auxDeclNGen_253_);
lean_inc(v_ngen_252_);
lean_inc(v_nextMacroScope_251_);
lean_inc(v_env_250_);
lean_dec(v___x_249_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_282_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = l_Lean_Environment_setExporting(v_env_250_, v_isExporting_243_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 5, v___x_244_);
lean_ctor_set(v___x_259_, 0, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_nextMacroScope_251_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_ngen_252_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_auxDeclNGen_253_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_traceState_254_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_messages_255_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_infoState_256_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_snapshotTasks_257_);
v___x_263_ = v_reuseFailAlloc_281_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_mctx_266_; lean_object* v_zetaDeltaFVarIds_267_; lean_object* v_postponed_268_; lean_object* v_diag_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_279_; 
v___x_264_ = lean_st_ref_put(v___y_242_, v___x_263_);
v___x_265_ = lean_st_ref_take(v___y_245_);
v_mctx_266_ = lean_ctor_get(v___x_265_, 0);
v_zetaDeltaFVarIds_267_ = lean_ctor_get(v___x_265_, 2);
v_postponed_268_ = lean_ctor_get(v___x_265_, 3);
v_diag_269_ = lean_ctor_get(v___x_265_, 4);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v___x_265_, 1);
lean_dec(v_unused_280_);
v___x_271_ = v___x_265_;
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_diag_269_);
lean_inc(v_postponed_268_);
lean_inc(v_zetaDeltaFVarIds_267_);
lean_inc(v_mctx_266_);
lean_dec(v___x_265_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 1, v___x_246_);
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_mctx_266_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_zetaDeltaFVarIds_267_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_postponed_268_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_diag_269_);
v___x_274_ = v_reuseFailAlloc_278_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_st_ref_put(v___y_245_, v___x_274_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_284_, lean_object* v_isExporting_285_, lean_object* v___x_286_, lean_object* v___y_287_, lean_object* v___x_288_, lean_object* v_a_x3f_289_, lean_object* v___y_290_){
_start:
{
uint8_t v_isExporting_boxed_291_; lean_object* v_res_292_; 
v_isExporting_boxed_291_ = lean_unbox(v_isExporting_285_);
v_res_292_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_284_, v_isExporting_boxed_291_, v___x_286_, v___y_287_, v___x_288_, v_a_x3f_289_);
lean_dec(v_a_x3f_289_);
lean_dec(v___y_287_);
lean_dec(v___y_284_);
return v_res_292_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_293_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1);
v___x_299_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
lean_ctor_set(v___x_299_, 2, v___x_298_);
lean_ctor_set(v___x_299_, 3, v___x_298_);
lean_ctor_set(v___x_299_, 4, v___x_298_);
lean_ctor_set(v___x_299_, 5, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(lean_object* v_x_300_, uint8_t v_isExporting_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_env_308_; uint8_t v_isExporting_309_; lean_object* v___x_375_; uint8_t v_isModule_376_; 
v___x_307_ = lean_st_ref_get(v___y_305_);
v_env_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc_ref(v_env_308_);
lean_dec(v___x_307_);
v_isExporting_309_ = lean_ctor_get_uint8(v_env_308_, sizeof(void*)*8);
v___x_375_ = l_Lean_Environment_header(v_env_308_);
lean_dec_ref(v_env_308_);
v_isModule_376_ = lean_ctor_get_uint8(v___x_375_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_375_);
if (v_isModule_376_ == 0)
{
lean_object* v___x_377_; 
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v___x_377_ = lean_apply_5(v_x_300_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, lean_box(0));
return v___x_377_;
}
else
{
if (v_isExporting_309_ == 0)
{
if (v_isExporting_301_ == 0)
{
lean_object* v___x_378_; 
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v___x_378_ = lean_apply_5(v_x_300_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, lean_box(0));
return v___x_378_;
}
else
{
goto v___jp_310_;
}
}
else
{
if (v_isExporting_301_ == 0)
{
goto v___jp_310_;
}
else
{
lean_object* v___x_379_; 
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v___x_379_ = lean_apply_5(v_x_300_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, lean_box(0));
return v___x_379_;
}
}
}
v___jp_310_:
{
lean_object* v___x_311_; lean_object* v_env_312_; lean_object* v_nextMacroScope_313_; lean_object* v_ngen_314_; lean_object* v_auxDeclNGen_315_; lean_object* v_traceState_316_; lean_object* v_messages_317_; lean_object* v_infoState_318_; lean_object* v_snapshotTasks_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_373_; 
v___x_311_ = lean_st_ref_take(v___y_305_);
v_env_312_ = lean_ctor_get(v___x_311_, 0);
v_nextMacroScope_313_ = lean_ctor_get(v___x_311_, 1);
v_ngen_314_ = lean_ctor_get(v___x_311_, 2);
v_auxDeclNGen_315_ = lean_ctor_get(v___x_311_, 3);
v_traceState_316_ = lean_ctor_get(v___x_311_, 4);
v_messages_317_ = lean_ctor_get(v___x_311_, 6);
v_infoState_318_ = lean_ctor_get(v___x_311_, 7);
v_snapshotTasks_319_ = lean_ctor_get(v___x_311_, 8);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v___x_311_, 5);
lean_dec(v_unused_374_);
v___x_321_ = v___x_311_;
v_isShared_322_ = v_isSharedCheck_373_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_snapshotTasks_319_);
lean_inc(v_infoState_318_);
lean_inc(v_messages_317_);
lean_inc(v_traceState_316_);
lean_inc(v_auxDeclNGen_315_);
lean_inc(v_ngen_314_);
lean_inc(v_nextMacroScope_313_);
lean_inc(v_env_312_);
lean_dec(v___x_311_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_373_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_323_ = l_Lean_Environment_setExporting(v_env_312_, v_isExporting_301_);
v___x_324_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 5, v___x_324_);
lean_ctor_set(v___x_321_, 0, v___x_323_);
v___x_326_ = v___x_321_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_nextMacroScope_313_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_ngen_314_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_auxDeclNGen_315_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v_traceState_316_);
lean_ctor_set(v_reuseFailAlloc_372_, 5, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_372_, 6, v_messages_317_);
lean_ctor_set(v_reuseFailAlloc_372_, 7, v_infoState_318_);
lean_ctor_set(v_reuseFailAlloc_372_, 8, v_snapshotTasks_319_);
v___x_326_ = v_reuseFailAlloc_372_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_mctx_329_; lean_object* v_zetaDeltaFVarIds_330_; lean_object* v_postponed_331_; lean_object* v_diag_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_370_; 
v___x_327_ = lean_st_ref_put(v___y_305_, v___x_326_);
v___x_328_ = lean_st_ref_take(v___y_303_);
v_mctx_329_ = lean_ctor_get(v___x_328_, 0);
v_zetaDeltaFVarIds_330_ = lean_ctor_get(v___x_328_, 2);
v_postponed_331_ = lean_ctor_get(v___x_328_, 3);
v_diag_332_ = lean_ctor_get(v___x_328_, 4);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_328_, 1);
lean_dec(v_unused_371_);
v___x_334_ = v___x_328_;
v_isShared_335_ = v_isSharedCheck_370_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_diag_332_);
lean_inc(v_postponed_331_);
lean_inc(v_zetaDeltaFVarIds_330_);
lean_inc(v_mctx_329_);
lean_dec(v___x_328_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_370_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 1, v___x_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_mctx_329_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_zetaDeltaFVarIds_330_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_postponed_331_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v_diag_332_);
v___x_338_ = v_reuseFailAlloc_369_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v_r_340_; 
v___x_339_ = lean_st_ref_put(v___y_303_, v___x_338_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v_r_340_ = lean_apply_5(v_x_300_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, lean_box(0));
if (lean_obj_tag(v_r_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_357_; 
v_a_341_ = lean_ctor_get(v_r_340_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v_r_340_);
if (v_isSharedCheck_357_ == 0)
{
v___x_343_ = v_r_340_;
v_isShared_344_ = v_isSharedCheck_357_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v_r_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_357_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
lean_inc(v_a_341_);
if (v_isShared_344_ == 0)
{
lean_ctor_set_tag(v___x_343_, 1);
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_356_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
v___x_347_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_305_, v_isExporting_309_, v___x_324_, v___y_303_, v___x_336_, v___x_346_);
lean_dec_ref(v___x_346_);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v___x_347_, 0);
lean_dec(v_unused_355_);
v___x_349_ = v___x_347_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_dec(v___x_347_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v_a_341_);
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_341_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_a_358_ = lean_ctor_get(v_r_340_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v_r_340_, 1);
v___x_359_ = lean_box(0);
v___x_360_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_305_, v_isExporting_309_, v___x_324_, v___y_303_, v___x_336_, v___x_359_);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; 
v_unused_368_ = lean_ctor_get(v___x_360_, 0);
lean_dec(v_unused_368_);
v___x_362_ = v___x_360_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_dec(v___x_360_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set_tag(v___x_362_, 1);
lean_ctor_set(v___x_362_, 0, v_a_358_);
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_358_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___boxed(lean_object* v_x_380_, lean_object* v_isExporting_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
uint8_t v_isExporting_boxed_387_; lean_object* v_res_388_; 
v_isExporting_boxed_387_ = lean_unbox(v_isExporting_381_);
v_res_388_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_380_, v_isExporting_boxed_387_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object* v_x_389_, uint8_t v_when_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
if (v_when_390_ == 0)
{
lean_object* v___x_396_; 
lean_inc(v___y_394_);
lean_inc_ref(v___y_393_);
lean_inc(v___y_392_);
lean_inc_ref(v___y_391_);
v___x_396_ = lean_apply_5(v_x_389_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, lean_box(0));
return v___x_396_;
}
else
{
uint8_t v___x_397_; lean_object* v___x_398_; 
v___x_397_ = 0;
v___x_398_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_389_, v___x_397_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object* v_x_399_, lean_object* v_when_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
uint8_t v_when_boxed_406_; lean_object* v_res_407_; 
v_when_boxed_406_ = lean_unbox(v_when_400_);
v_res_407_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_399_, v_when_boxed_406_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object* v_e_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; lean_object* v_env_415_; lean_object* v___f_416_; uint8_t v___x_417_; lean_object* v___x_418_; 
v___x_414_ = lean_st_ref_get(v_a_412_);
v_env_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc_ref(v_env_415_);
lean_dec(v___x_414_);
v___f_416_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed), 7, 2);
lean_closure_set(v___f_416_, 0, v_e_408_);
lean_closure_set(v___f_416_, 1, v_env_415_);
v___x_417_ = 1;
v___x_418_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v___f_416_, v___x_417_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object* v_e_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(uint8_t v_a_426_, uint8_t v___x_427_, lean_object* v___x_428_, lean_object* v_x_429_, lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_a_426_, v___x_427_, v___x_428_, v_x_429_, v_x_430_, v_x_431_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object* v_a_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
uint8_t v_a_4759__boxed_449_; uint8_t v___x_4760__boxed_450_; lean_object* v_res_451_; 
v_a_4759__boxed_449_ = lean_unbox(v_a_438_);
v___x_4760__boxed_450_ = lean_unbox(v___x_439_);
v_res_451_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(v_a_4759__boxed_449_, v___x_4760__boxed_450_, v___x_440_, v_x_441_, v_x_442_, v_x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(lean_object* v_00_u03b1_452_, lean_object* v_x_453_, uint8_t v_isExporting_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_453_, v_isExporting_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___boxed(lean_object* v_00_u03b1_461_, lean_object* v_x_462_, lean_object* v_isExporting_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
uint8_t v_isExporting_boxed_469_; lean_object* v_res_470_; 
v_isExporting_boxed_469_ = lean_unbox(v_isExporting_463_);
v_res_470_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(v_00_u03b1_461_, v_x_462_, v_isExporting_boxed_469_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object* v_00_u03b1_471_, lean_object* v_x_472_, uint8_t v_when_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_472_, v_when_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object* v_00_u03b1_480_, lean_object* v_x_481_, lean_object* v_when_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
uint8_t v_when_boxed_488_; lean_object* v_res_489_; 
v_when_boxed_488_ = lean_unbox(v_when_482_);
v_res_489_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(v_00_u03b1_480_, v_x_481_, v_when_boxed_488_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(lean_object* v_x_490_, uint8_t v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_box(v___y_491_);
lean_inc(v___y_492_);
v___x_499_ = lean_apply_7(v_x_490_, v___x_498_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, lean_box(0));
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed(lean_object* v_x_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v___y_33355__boxed_508_; lean_object* v_res_509_; 
v___y_33355__boxed_508_ = lean_unbox(v___y_501_);
v_res_509_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(v_x_500_, v___y_33355__boxed_508_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_502_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object* v_lctx_510_, lean_object* v_localInsts_511_, lean_object* v_x_512_, uint8_t v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; lean_object* v___f_521_; lean_object* v___x_522_; 
v___x_520_ = lean_box(v___y_513_);
lean_inc(v___y_514_);
v___f_521_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_521_, 0, v_x_512_);
lean_closure_set(v___f_521_, 1, v___x_520_);
lean_closure_set(v___f_521_, 2, v___y_514_);
v___x_522_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_510_, v_localInsts_511_, v___f_521_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_522_) == 0)
{
return v___x_522_;
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object* v_lctx_531_, lean_object* v_localInsts_532_, lean_object* v_x_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint8_t v___y_33380__boxed_541_; lean_object* v_res_542_; 
v___y_33380__boxed_541_ = lean_unbox(v___y_534_);
v_res_542_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_lctx_531_, v_localInsts_532_, v_x_533_, v___y_33380__boxed_541_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object* v_00_u03b1_543_, lean_object* v_lctx_544_, lean_object* v_localInsts_545_, lean_object* v_x_546_, uint8_t v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_lctx_544_, v_localInsts_545_, v_x_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object* v_00_u03b1_555_, lean_object* v_lctx_556_, lean_object* v_localInsts_557_, lean_object* v_x_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
uint8_t v___y_33424__boxed_566_; lean_object* v_res_567_; 
v___y_33424__boxed_566_ = lean_unbox(v___y_559_);
v_res_567_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(v_00_u03b1_555_, v_lctx_556_, v_localInsts_557_, v_x_558_, v___y_33424__boxed_566_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___lam__0(lean_object* v_k_568_, uint8_t v___y_569_, lean_object* v___y_570_, lean_object* v_b_571_, lean_object* v_c_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_box(v___y_569_);
lean_inc(v___y_576_);
lean_inc_ref(v___y_575_);
lean_inc(v___y_574_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_570_);
v___x_579_ = lean_apply_9(v_k_568_, v_b_571_, v_c_572_, v___x_578_, v___y_570_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, lean_box(0));
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___lam__0___boxed(lean_object* v_k_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v_b_583_, lean_object* v_c_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
uint8_t v___y_33447__boxed_590_; lean_object* v_res_591_; 
v___y_33447__boxed_590_ = lean_unbox(v___y_581_);
v_res_591_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___lam__0(v_k_580_, v___y_33447__boxed_590_, v___y_582_, v_b_583_, v_c_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_582_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(lean_object* v_e_592_, lean_object* v_k_593_, uint8_t v_cleanupAnnotations_594_, uint8_t v_preserveNondepLet_595_, uint8_t v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; lean_object* v___f_604_; uint8_t v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_603_ = lean_box(v___y_596_);
lean_inc(v___y_597_);
v___f_604_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_604_, 0, v_k_593_);
lean_closure_set(v___f_604_, 1, v___x_603_);
lean_closure_set(v___f_604_, 2, v___y_597_);
v___x_605_ = 1;
v___x_606_ = 0;
v___x_607_ = lean_box(0);
v___x_608_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_592_, v___x_605_, v___x_605_, v_preserveNondepLet_595_, v___x_606_, v___x_607_, v___f_604_, v_cleanupAnnotations_594_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
if (lean_obj_tag(v___x_608_) == 0)
{
return v___x_608_;
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___boxed(lean_object* v_e_617_, lean_object* v_k_618_, lean_object* v_cleanupAnnotations_619_, lean_object* v_preserveNondepLet_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_628_; uint8_t v_preserveNondepLet_boxed_629_; uint8_t v___y_33472__boxed_630_; lean_object* v_res_631_; 
v_cleanupAnnotations_boxed_628_ = lean_unbox(v_cleanupAnnotations_619_);
v_preserveNondepLet_boxed_629_ = lean_unbox(v_preserveNondepLet_620_);
v___y_33472__boxed_630_ = lean_unbox(v___y_621_);
v_res_631_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_e_617_, v_k_618_, v_cleanupAnnotations_boxed_628_, v_preserveNondepLet_boxed_629_, v___y_33472__boxed_630_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object* v_00_u03b1_632_, lean_object* v_e_633_, lean_object* v_k_634_, uint8_t v_cleanupAnnotations_635_, uint8_t v_preserveNondepLet_636_, uint8_t v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_e_633_, v_k_634_, v_cleanupAnnotations_635_, v_preserveNondepLet_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object* v_00_u03b1_645_, lean_object* v_e_646_, lean_object* v_k_647_, lean_object* v_cleanupAnnotations_648_, lean_object* v_preserveNondepLet_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_657_; uint8_t v_preserveNondepLet_boxed_658_; uint8_t v___y_33522__boxed_659_; lean_object* v_res_660_; 
v_cleanupAnnotations_boxed_657_ = lean_unbox(v_cleanupAnnotations_648_);
v_preserveNondepLet_boxed_658_ = lean_unbox(v_preserveNondepLet_649_);
v___y_33522__boxed_659_ = lean_unbox(v___y_650_);
v_res_660_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_00_u03b1_645_, v_e_646_, v_k_647_, v_cleanupAnnotations_boxed_657_, v_preserveNondepLet_boxed_658_, v___y_33522__boxed_659_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___redArg(lean_object* v_type_661_, lean_object* v_k_662_, uint8_t v_cleanupAnnotations_663_, uint8_t v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; lean_object* v___f_672_; uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_671_ = lean_box(v___y_664_);
lean_inc(v___y_665_);
v___f_672_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_672_, 0, v_k_662_);
lean_closure_set(v___f_672_, 1, v___x_671_);
lean_closure_set(v___f_672_, 2, v___y_665_);
v___x_673_ = 0;
v___x_674_ = lean_box(0);
v___x_675_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_673_, v___x_674_, v_type_661_, v___f_672_, v_cleanupAnnotations_663_, v___x_673_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_675_) == 0)
{
return v___x_675_;
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___redArg___boxed(lean_object* v_type_684_, lean_object* v_k_685_, lean_object* v_cleanupAnnotations_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_694_; uint8_t v___y_33545__boxed_695_; lean_object* v_res_696_; 
v_cleanupAnnotations_boxed_694_ = lean_unbox(v_cleanupAnnotations_686_);
v___y_33545__boxed_695_ = lean_unbox(v___y_687_);
v_res_696_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___redArg(v_type_684_, v_k_685_, v_cleanupAnnotations_boxed_694_, v___y_33545__boxed_695_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object* v_00_u03b1_697_, lean_object* v_type_698_, lean_object* v_k_699_, uint8_t v_cleanupAnnotations_700_, uint8_t v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___redArg(v_type_698_, v_k_699_, v_cleanupAnnotations_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object* v_00_u03b1_709_, lean_object* v_type_710_, lean_object* v_k_711_, lean_object* v_cleanupAnnotations_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_720_; uint8_t v___y_33593__boxed_721_; lean_object* v_res_722_; 
v_cleanupAnnotations_boxed_720_ = lean_unbox(v_cleanupAnnotations_712_);
v___y_33593__boxed_721_ = lean_unbox(v___y_713_);
v_res_722_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_00_u03b1_709_, v_type_710_, v_k_711_, v_cleanupAnnotations_boxed_720_, v___y_33593__boxed_721_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7_spec__12___redArg(lean_object* v_x_723_, uint8_t v_isExporting_724_, uint8_t v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; lean_object* v_env_733_; uint8_t v_isExporting_734_; lean_object* v___x_801_; uint8_t v_isModule_802_; 
v___x_732_ = lean_st_ref_get(v___y_730_);
v_env_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc_ref(v_env_733_);
lean_dec(v___x_732_);
v_isExporting_734_ = lean_ctor_get_uint8(v_env_733_, sizeof(void*)*8);
v___x_801_ = l_Lean_Environment_header(v_env_733_);
lean_dec_ref(v_env_733_);
v_isModule_802_ = lean_ctor_get_uint8(v___x_801_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_801_);
if (v_isModule_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_box(v___y_725_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_726_);
v___x_804_ = lean_apply_7(v_x_723_, v___x_803_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, lean_box(0));
return v___x_804_;
}
else
{
if (v_isExporting_734_ == 0)
{
if (v_isExporting_724_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_box(v___y_725_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_726_);
v___x_806_ = lean_apply_7(v_x_723_, v___x_805_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, lean_box(0));
return v___x_806_;
}
else
{
goto v___jp_735_;
}
}
else
{
if (v_isExporting_724_ == 0)
{
goto v___jp_735_;
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_box(v___y_725_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_726_);
v___x_808_ = lean_apply_7(v_x_723_, v___x_807_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, lean_box(0));
return v___x_808_;
}
}
}
v___jp_735_:
{
lean_object* v___x_736_; lean_object* v_env_737_; lean_object* v_nextMacroScope_738_; lean_object* v_ngen_739_; lean_object* v_auxDeclNGen_740_; lean_object* v_traceState_741_; lean_object* v_messages_742_; lean_object* v_infoState_743_; lean_object* v_snapshotTasks_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_799_; 
v___x_736_ = lean_st_ref_take(v___y_730_);
v_env_737_ = lean_ctor_get(v___x_736_, 0);
v_nextMacroScope_738_ = lean_ctor_get(v___x_736_, 1);
v_ngen_739_ = lean_ctor_get(v___x_736_, 2);
v_auxDeclNGen_740_ = lean_ctor_get(v___x_736_, 3);
v_traceState_741_ = lean_ctor_get(v___x_736_, 4);
v_messages_742_ = lean_ctor_get(v___x_736_, 6);
v_infoState_743_ = lean_ctor_get(v___x_736_, 7);
v_snapshotTasks_744_ = lean_ctor_get(v___x_736_, 8);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; 
v_unused_800_ = lean_ctor_get(v___x_736_, 5);
lean_dec(v_unused_800_);
v___x_746_ = v___x_736_;
v_isShared_747_ = v_isSharedCheck_799_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snapshotTasks_744_);
lean_inc(v_infoState_743_);
lean_inc(v_messages_742_);
lean_inc(v_traceState_741_);
lean_inc(v_auxDeclNGen_740_);
lean_inc(v_ngen_739_);
lean_inc(v_nextMacroScope_738_);
lean_inc(v_env_737_);
lean_dec(v___x_736_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_799_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_748_ = l_Lean_Environment_setExporting(v_env_737_, v_isExporting_724_);
v___x_749_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 5, v___x_749_);
lean_ctor_set(v___x_746_, 0, v___x_748_);
v___x_751_ = v___x_746_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_nextMacroScope_738_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_ngen_739_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_auxDeclNGen_740_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_traceState_741_);
lean_ctor_set(v_reuseFailAlloc_798_, 5, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_798_, 6, v_messages_742_);
lean_ctor_set(v_reuseFailAlloc_798_, 7, v_infoState_743_);
lean_ctor_set(v_reuseFailAlloc_798_, 8, v_snapshotTasks_744_);
v___x_751_ = v_reuseFailAlloc_798_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_mctx_754_; lean_object* v_zetaDeltaFVarIds_755_; lean_object* v_postponed_756_; lean_object* v_diag_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_796_; 
v___x_752_ = lean_st_ref_put(v___y_730_, v___x_751_);
v___x_753_ = lean_st_ref_take(v___y_728_);
v_mctx_754_ = lean_ctor_get(v___x_753_, 0);
v_zetaDeltaFVarIds_755_ = lean_ctor_get(v___x_753_, 2);
v_postponed_756_ = lean_ctor_get(v___x_753_, 3);
v_diag_757_ = lean_ctor_get(v___x_753_, 4);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v___x_753_, 1);
lean_dec(v_unused_797_);
v___x_759_ = v___x_753_;
v_isShared_760_ = v_isSharedCheck_796_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_diag_757_);
lean_inc(v_postponed_756_);
lean_inc(v_zetaDeltaFVarIds_755_);
lean_inc(v_mctx_754_);
lean_dec(v___x_753_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_796_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v___x_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_mctx_754_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_zetaDeltaFVarIds_755_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_postponed_756_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_diag_757_);
v___x_763_ = v_reuseFailAlloc_795_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_r_766_; 
v___x_764_ = lean_st_ref_put(v___y_728_, v___x_763_);
v___x_765_ = lean_box(v___y_725_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_726_);
v_r_766_ = lean_apply_7(v_x_723_, v___x_765_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, lean_box(0));
if (lean_obj_tag(v_r_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_783_; 
v_a_767_ = lean_ctor_get(v_r_766_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_r_766_);
if (v_isSharedCheck_783_ == 0)
{
v___x_769_ = v_r_766_;
v_isShared_770_ = v_isSharedCheck_783_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v_r_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_783_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
lean_inc(v_a_767_);
if (v_isShared_770_ == 0)
{
lean_ctor_set_tag(v___x_769_, 1);
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_782_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v___x_773_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_730_, v_isExporting_734_, v___x_749_, v___y_728_, v___x_761_, v___x_772_);
lean_dec_ref(v___x_772_);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_773_, 0);
lean_dec(v_unused_781_);
v___x_775_ = v___x_773_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_dec(v___x_773_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v_a_767_);
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_767_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_784_ = lean_ctor_get(v_r_766_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v_r_766_, 1);
v___x_785_ = lean_box(0);
v___x_786_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_730_, v_isExporting_734_, v___x_749_, v___y_728_, v___x_761_, v___x_785_);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v___x_786_, 0);
lean_dec(v_unused_794_);
v___x_788_ = v___x_786_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_dec(v___x_786_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set_tag(v___x_788_, 1);
lean_ctor_set(v___x_788_, 0, v_a_784_);
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_784_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7_spec__12___redArg___boxed(lean_object* v_x_809_, lean_object* v_isExporting_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
uint8_t v_isExporting_boxed_818_; uint8_t v___y_33629__boxed_819_; lean_object* v_res_820_; 
v_isExporting_boxed_818_ = lean_unbox(v_isExporting_810_);
v___y_33629__boxed_819_ = lean_unbox(v___y_811_);
v_res_820_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7_spec__12___redArg(v_x_809_, v_isExporting_boxed_818_, v___y_33629__boxed_819_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(lean_object* v_x_821_, uint8_t v_when_822_, uint8_t v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
if (v_when_822_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_box(v___y_823_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v___y_824_);
v___x_831_ = lean_apply_7(v_x_821_, v___x_830_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, lean_box(0));
return v___x_831_;
}
else
{
uint8_t v___x_832_; lean_object* v___x_833_; 
v___x_832_ = 0;
v___x_833_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7_spec__12___redArg(v_x_821_, v___x_832_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg___boxed(lean_object* v_x_834_, lean_object* v_when_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
uint8_t v_when_boxed_843_; uint8_t v___y_33778__boxed_844_; lean_object* v_res_845_; 
v_when_boxed_843_ = lean_unbox(v_when_835_);
v___y_33778__boxed_844_ = lean_unbox(v___y_836_);
v_res_845_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_x_834_, v_when_boxed_843_, v___y_33778__boxed_844_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___lam__0(lean_object* v_proof_846_, uint8_t v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; 
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
v___x_854_ = lean_infer_type(v_proof_846_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___lam__0___boxed(lean_object* v_proof_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
uint8_t v___y_33807__boxed_863_; lean_object* v_res_864_; 
v___y_33807__boxed_863_ = lean_unbox(v___y_856_);
v_res_864_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___lam__0(v_proof_855_, v___y_33807__boxed_863_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object* v_proof_865_, uint8_t v_cache_866_, lean_object* v_postprocessType_867_, uint8_t v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___f_875_; uint8_t v___x_876_; lean_object* v___x_877_; 
lean_inc_ref(v_proof_865_);
v___f_875_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_875_, 0, v_proof_865_);
v___x_876_ = 1;
v___x_877_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v___f_875_, v___x_876_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
v___x_879_ = l_Lean_Core_betaReduce(v_a_878_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_881_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_879_, 1);
v___x_881_ = l_Lean_Meta_zetaReduce(v_a_880_, v___x_876_, v___x_876_, v___x_876_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = lean_box(v___y_868_);
lean_inc(v___y_873_);
lean_inc_ref(v___y_872_);
lean_inc(v___y_871_);
lean_inc_ref(v___y_870_);
lean_inc(v___y_869_);
v___x_884_ = lean_apply_8(v_postprocessType_867_, v_a_882_, v___x_883_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, lean_box(0));
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; uint8_t v___y_887_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
if (v_cache_866_ == 0)
{
v___y_887_ = v_cache_866_;
goto v___jp_886_;
}
else
{
uint8_t v___x_890_; 
v___x_890_ = l_Lean_Expr_hasSorry(v_proof_865_);
if (v___x_890_ == 0)
{
v___y_887_ = v_cache_866_;
goto v___jp_886_;
}
else
{
uint8_t v___x_891_; 
v___x_891_ = 0;
v___y_887_ = v___x_891_;
goto v___jp_886_;
}
}
v___jp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_box(0);
v___x_889_ = l_Lean_Meta_mkAuxTheorem(v_a_885_, v_proof_865_, v___x_876_, v___x_888_, v___y_887_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
return v___x_889_;
}
}
else
{
lean_dec_ref(v_proof_865_);
return v___x_884_;
}
}
else
{
lean_dec_ref(v_postprocessType_867_);
lean_dec_ref(v_proof_865_);
return v___x_881_;
}
}
else
{
lean_dec_ref(v_postprocessType_867_);
lean_dec_ref(v_proof_865_);
return v___x_879_;
}
}
else
{
lean_dec_ref(v_postprocessType_867_);
lean_dec_ref(v_proof_865_);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___boxed(lean_object* v_proof_892_, lean_object* v_cache_893_, lean_object* v_postprocessType_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
uint8_t v_cache_boxed_902_; uint8_t v___y_33830__boxed_903_; lean_object* v_res_904_; 
v_cache_boxed_902_ = lean_unbox(v_cache_893_);
v___y_33830__boxed_903_ = lean_unbox(v___y_895_);
v_res_904_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(v_proof_892_, v_cache_boxed_902_, v_postprocessType_894_, v___y_33830__boxed_903_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object* v_m_905_, lean_object* v_query_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
lean_object* v_zero_910_; uint8_t v_isZero_911_; 
v_zero_910_ = lean_unsigned_to_nat(0u);
v_isZero_911_ = lean_nat_dec_eq(v_x_908_, v_zero_910_);
if (v_isZero_911_ == 1)
{
lean_dec(v_x_909_);
lean_dec(v_x_908_);
if (lean_obj_tag(v_x_907_) == 0)
{
lean_object* v___x_912_; 
v___x_912_ = lean_box(2);
return v___x_912_;
}
else
{
lean_object* v_val_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
v_val_913_ = lean_ctor_get(v_x_907_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v_x_907_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v_x_907_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_val_913_);
lean_dec(v_x_907_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_val_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_keyArray_921_; lean_object* v_valueArray_922_; lean_object* v___x_923_; uint8_t v_isSome_924_; 
v_keyArray_921_ = lean_ctor_get(v_m_905_, 1);
v_valueArray_922_ = lean_ctor_get(v_m_905_, 2);
v___x_923_ = lean_array_fget_borrowed(v_keyArray_921_, v_x_909_);
v_isSome_924_ = lean_noption_is_some(v___x_923_);
if (v_isSome_924_ == 0)
{
lean_dec(v_x_908_);
if (lean_obj_tag(v_x_907_) == 0)
{
lean_object* v___x_925_; 
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v_x_909_);
return v___x_925_;
}
else
{
lean_object* v_val_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_x_909_);
v_val_926_ = lean_ctor_get(v_x_907_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v_x_907_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v_x_907_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_val_926_);
lean_dec(v_x_907_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_val_926_);
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
else
{
lean_object* v_one_934_; lean_object* v_n_935_; lean_object* v___y_937_; 
v_one_934_ = lean_unsigned_to_nat(1u);
v_n_935_ = lean_nat_sub(v_x_908_, v_one_934_);
lean_dec(v_x_908_);
if (v_isSome_924_ == 0)
{
goto v___jp_943_;
}
else
{
lean_object* v___x_945_; uint8_t v_isSome_946_; 
v___x_945_ = lean_array_fget_borrowed(v_valueArray_922_, v_x_909_);
v_isSome_946_ = lean_noption_is_some(v___x_945_);
if (v_isSome_946_ == 0)
{
goto v___jp_943_;
}
else
{
lean_object* v_val_947_; uint8_t v___x_948_; 
lean_inc(v___x_923_);
v_val_947_ = lean_noption_get(v___x_923_);
v___x_948_ = l_Lean_ExprStructEq_beq(v_val_947_, v_query_906_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
lean_dec(v_val_947_);
v___x_949_ = lean_array_get_size(v_keyArray_921_);
v___x_950_ = lean_nat_add(v_x_909_, v_one_934_);
lean_dec(v_x_909_);
v___x_951_ = lean_nat_dec_lt(v___x_950_, v___x_949_);
if (v___x_951_ == 0)
{
lean_dec(v___x_950_);
v_x_908_ = v_n_935_;
v_x_909_ = v_zero_910_;
goto _start;
}
else
{
v_x_908_ = v_n_935_;
v_x_909_ = v___x_950_;
goto _start;
}
}
else
{
lean_object* v_val_954_; lean_object* v___x_955_; 
lean_dec(v_n_935_);
lean_dec(v_x_907_);
lean_inc(v___x_945_);
v_val_954_ = lean_noption_get(v___x_945_);
v___x_955_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_955_, 0, v_x_909_);
lean_ctor_set(v___x_955_, 1, v_val_947_);
lean_ctor_set(v___x_955_, 2, v_val_954_);
return v___x_955_;
}
}
}
v___jp_936_:
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_938_ = lean_array_get_size(v_keyArray_921_);
v___x_939_ = lean_nat_add(v_x_909_, v_one_934_);
lean_dec(v_x_909_);
v___x_940_ = lean_nat_dec_lt(v___x_939_, v___x_938_);
if (v___x_940_ == 0)
{
lean_dec(v___x_939_);
v_x_907_ = v___y_937_;
v_x_908_ = v_n_935_;
v_x_909_ = v_zero_910_;
goto _start;
}
else
{
v_x_907_ = v___y_937_;
v_x_908_ = v_n_935_;
v_x_909_ = v___x_939_;
goto _start;
}
}
v___jp_943_:
{
if (lean_obj_tag(v_x_907_) == 0)
{
lean_object* v___x_944_; 
lean_inc(v_x_909_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_x_909_);
v___y_937_ = v___x_944_;
goto v___jp_936_;
}
else
{
v___y_937_ = v_x_907_;
goto v___jp_936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object* v_m_956_, lean_object* v_query_957_, lean_object* v_x_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_m_956_, v_query_957_, v_x_958_, v_x_959_, v_x_960_);
lean_dec_ref(v_query_957_);
lean_dec_ref(v_m_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object* v_m_962_, lean_object* v_query_963_){
_start:
{
lean_object* v_keyArray_964_; lean_object* v___x_965_; uint64_t v___x_966_; uint64_t v___x_967_; uint64_t v___x_968_; uint64_t v_fold_969_; uint64_t v___x_970_; uint64_t v___x_971_; uint64_t v___x_972_; size_t v___x_973_; size_t v___x_974_; size_t v___x_975_; size_t v___x_976_; size_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_keyArray_964_ = lean_ctor_get(v_m_962_, 1);
v___x_965_ = lean_array_get_size(v_keyArray_964_);
v___x_966_ = l_Lean_ExprStructEq_hash(v_query_963_);
v___x_967_ = 32ULL;
v___x_968_ = lean_uint64_shift_right(v___x_966_, v___x_967_);
v_fold_969_ = lean_uint64_xor(v___x_966_, v___x_968_);
v___x_970_ = 16ULL;
v___x_971_ = lean_uint64_shift_right(v_fold_969_, v___x_970_);
v___x_972_ = lean_uint64_xor(v_fold_969_, v___x_971_);
v___x_973_ = lean_uint64_to_usize(v___x_972_);
v___x_974_ = lean_usize_of_nat(v___x_965_);
v___x_975_ = ((size_t)1ULL);
v___x_976_ = lean_usize_sub(v___x_974_, v___x_975_);
v___x_977_ = lean_usize_land(v___x_973_, v___x_976_);
v___x_978_ = lean_usize_to_nat(v___x_977_);
v___x_979_ = lean_box(0);
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_m_962_, v_query_963_, v___x_979_, v___x_965_, v___x_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg___boxed(lean_object* v_m_981_, lean_object* v_query_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_m_981_, v_query_982_);
lean_dec_ref(v_query_982_);
lean_dec_ref(v_m_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__5___redArg(lean_object* v_m_984_, lean_object* v_query_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_m_984_, v_query_985_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_index_987_; lean_object* v_key_988_; lean_object* v_value_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
v_index_987_ = lean_ctor_get(v___x_986_, 0);
v_key_988_ = lean_ctor_get(v___x_986_, 1);
v_value_989_ = lean_ctor_get(v___x_986_, 2);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_986_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_value_989_);
lean_inc(v_key_988_);
lean_inc(v_index_987_);
lean_dec(v___x_986_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_index_987_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_key_988_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_value_989_);
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
lean_object* v___x_997_; 
lean_dec(v___x_986_);
v___x_997_ = lean_box(1);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__5___redArg___boxed(lean_object* v_m_998_, lean_object* v_query_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__5___redArg(v_m_998_, v_query_999_);
lean_dec_ref(v_query_999_);
lean_dec_ref(v_m_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object* v_m_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__5___redArg(v_m_1001_, v_a_1002_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_value_1004_; lean_object* v___x_1005_; 
v_value_1004_ = lean_ctor_get(v___x_1003_, 2);
lean_inc(v_value_1004_);
lean_dec_ref_known(v___x_1003_, 3);
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_value_1004_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_box(0);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___boxed(lean_object* v_m_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_m_1007_, v_a_1008_);
lean_dec_ref(v_a_1008_);
lean_dec_ref(v_m_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3_spec__7___redArg(lean_object* v_b_1010_, lean_object* v_acc_1011_, lean_object* v_i_1012_){
_start:
{
lean_object* v___y_1014_; lean_object* v_keyArray_1022_; lean_object* v_valueArray_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v_keyArray_1022_ = lean_ctor_get(v_b_1010_, 1);
v_valueArray_1023_ = lean_ctor_get(v_b_1010_, 2);
v___x_1024_ = lean_array_get_size(v_keyArray_1022_);
v___x_1025_ = lean_nat_dec_lt(v_i_1012_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_dec(v_i_1012_);
return v_acc_1011_;
}
else
{
lean_object* v___x_1026_; uint8_t v_isSome_1027_; 
v___x_1026_ = lean_array_fget_borrowed(v_keyArray_1022_, v_i_1012_);
v_isSome_1027_ = lean_noption_is_some(v___x_1026_);
if (v_isSome_1027_ == 0)
{
goto v___jp_1018_;
}
else
{
lean_object* v___x_1028_; uint8_t v_isSome_1029_; 
v___x_1028_ = lean_array_fget_borrowed(v_valueArray_1023_, v_i_1012_);
v_isSome_1029_ = lean_noption_is_some(v___x_1028_);
if (v_isSome_1029_ == 0)
{
goto v___jp_1018_;
}
else
{
lean_object* v_val_1030_; lean_object* v_val_1031_; lean_object* v_i_1033_; lean_object* v___x_1038_; 
lean_inc(v___x_1026_);
v_val_1030_ = lean_noption_get(v___x_1026_);
lean_inc(v___x_1028_);
v_val_1031_ = lean_noption_get(v___x_1028_);
v___x_1038_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_acc_1011_, v_val_1030_);
switch(lean_obj_tag(v___x_1038_))
{
case 0:
{
lean_object* v_index_1039_; lean_object* v_size_1040_; lean_object* v___x_1041_; 
v_index_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_index_1039_);
lean_dec_ref_known(v___x_1038_, 3);
v_size_1040_ = lean_ctor_get(v_acc_1011_, 0);
lean_inc(v_size_1040_);
v___x_1041_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1011_, v_size_1040_, v_index_1039_, v_val_1030_, v_val_1031_);
lean_dec(v_index_1039_);
v___y_1014_ = v___x_1041_;
goto v___jp_1013_;
}
case 1:
{
lean_object* v_index_1042_; 
v_index_1042_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_index_1042_);
lean_dec_ref_known(v___x_1038_, 1);
v_i_1033_ = v_index_1042_;
goto v___jp_1032_;
}
default: 
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1011_, v___x_1043_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_index_1045_; 
v_index_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_index_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v_i_1033_ = v_index_1045_;
goto v___jp_1032_;
}
else
{
lean_dec(v_val_1031_);
lean_dec(v_val_1030_);
v___y_1014_ = v_acc_1011_;
goto v___jp_1013_;
}
}
}
v___jp_1032_:
{
lean_object* v_size_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_size_1034_ = lean_ctor_get(v_acc_1011_, 0);
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = lean_nat_add(v_size_1034_, v___x_1035_);
v___x_1037_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1011_, v___x_1036_, v_i_1033_, v_val_1030_, v_val_1031_);
lean_dec(v_i_1033_);
v___y_1014_ = v___x_1037_;
goto v___jp_1013_;
}
}
}
}
v___jp_1013_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_add(v_i_1012_, v___x_1015_);
lean_dec(v_i_1012_);
v_acc_1011_ = v___y_1014_;
v_i_1012_ = v___x_1016_;
goto _start;
}
v___jp_1018_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_nat_add(v_i_1012_, v___x_1019_);
lean_dec(v_i_1012_);
v_i_1012_ = v___x_1020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_b_1046_, lean_object* v_acc_1047_, lean_object* v_i_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3_spec__7___redArg(v_b_1046_, v_acc_1047_, v_i_1048_);
lean_dec_ref(v_b_1046_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3___redArg(lean_object* v_init_1050_, lean_object* v_b_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3_spec__7___redArg(v_b_1051_, v_init_1050_, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3___redArg___boxed(lean_object* v_init_1054_, lean_object* v_b_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3___redArg(v_init_1054_, v_b_1055_);
lean_dec_ref(v_b_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(lean_object* v_m_1057_){
_start:
{
lean_object* v_keyArray_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v_cellCount_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_target_1065_; lean_object* v___x_1066_; 
v_keyArray_1058_ = lean_ctor_get(v_m_1057_, 1);
v___x_1059_ = lean_array_get_size(v_keyArray_1058_);
v___x_1060_ = lean_unsigned_to_nat(2u);
v_cellCount_1061_ = lean_nat_mul(v___x_1059_, v___x_1060_);
v___x_1062_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1061_);
v___x_1063_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1061_);
v___x_1064_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1061_);
v_target_1065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1065_, 0, v___x_1062_);
lean_ctor_set(v_target_1065_, 1, v___x_1063_);
lean_ctor_set(v_target_1065_, 2, v___x_1064_);
v___x_1066_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3___redArg(v_target_1065_, v_m_1057_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg___boxed(lean_object* v_m_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_1067_);
lean_dec_ref(v_m_1067_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__15_spec__18___redArg(lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
lean_object* v_ks_1073_; lean_object* v_vs_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1098_; 
v_ks_1073_ = lean_ctor_get(v_x_1069_, 0);
v_vs_1074_ = lean_ctor_get(v_x_1069_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_x_1069_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1076_ = v_x_1069_;
v_isShared_1077_ = v_isSharedCheck_1098_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_vs_1074_);
lean_inc(v_ks_1073_);
lean_dec(v_x_1069_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1098_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_array_get_size(v_ks_1073_);
v___x_1079_ = lean_nat_dec_lt(v_x_1070_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
lean_dec(v_x_1070_);
v___x_1080_ = lean_array_push(v_ks_1073_, v_x_1071_);
v___x_1081_ = lean_array_push(v_vs_1074_, v_x_1072_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v___x_1081_);
lean_ctor_set(v___x_1076_, 0, v___x_1080_);
v___x_1083_ = v___x_1076_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
else
{
lean_object* v_k_x27_1085_; uint8_t v___x_1086_; 
v_k_x27_1085_ = lean_array_fget_borrowed(v_ks_1073_, v_x_1070_);
v___x_1086_ = l_Lean_instBEqFVarId_beq(v_x_1071_, v_k_x27_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1088_; 
if (v_isShared_1077_ == 0)
{
v___x_1088_ = v___x_1076_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_ks_1073_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_vs_1074_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = lean_nat_add(v_x_1070_, v___x_1089_);
lean_dec(v_x_1070_);
v_x_1069_ = v___x_1088_;
v_x_1070_ = v___x_1090_;
goto _start;
}
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1093_ = lean_array_fset(v_ks_1073_, v_x_1070_, v_x_1071_);
v___x_1094_ = lean_array_fset(v_vs_1074_, v_x_1070_, v_x_1072_);
lean_dec(v_x_1070_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v___x_1094_);
lean_ctor_set(v___x_1076_, 0, v___x_1093_);
v___x_1096_ = v___x_1076_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__15___redArg(lean_object* v_n_1099_, lean_object* v_k_1100_, lean_object* v_v_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__15_spec__18___redArg(v_n_1099_, v___x_1102_, v_k_1100_, v_v_1101_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(lean_object* v_x_1105_, size_t v_x_1106_, size_t v_x_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
if (lean_obj_tag(v_x_1105_) == 0)
{
lean_object* v_es_1110_; size_t v___x_1111_; size_t v___x_1112_; lean_object* v_j_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_es_1110_ = lean_ctor_get(v_x_1105_, 0);
v___x_1111_ = ((size_t)31ULL);
v___x_1112_ = lean_usize_land(v_x_1106_, v___x_1111_);
v_j_1113_ = lean_usize_to_nat(v___x_1112_);
v___x_1114_ = lean_array_get_size(v_es_1110_);
v___x_1115_ = lean_nat_dec_lt(v_j_1113_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_dec(v_j_1113_);
lean_dec(v_x_1109_);
lean_dec(v_x_1108_);
return v_x_1105_;
}
else
{
lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1154_; 
lean_inc_ref(v_es_1110_);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_x_1105_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v_x_1105_, 0);
lean_dec(v_unused_1155_);
v___x_1117_ = v_x_1105_;
v_isShared_1118_ = v_isSharedCheck_1154_;
goto v_resetjp_1116_;
}
else
{
lean_dec(v_x_1105_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1154_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v_v_1119_; lean_object* v___x_1120_; lean_object* v_xs_x27_1121_; lean_object* v___y_1123_; 
v_v_1119_ = lean_array_fget(v_es_1110_, v_j_1113_);
v___x_1120_ = lean_box(0);
v_xs_x27_1121_ = lean_array_fset(v_es_1110_, v_j_1113_, v___x_1120_);
switch(lean_obj_tag(v_v_1119_))
{
case 0:
{
lean_object* v_key_1128_; lean_object* v_val_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1139_; 
v_key_1128_ = lean_ctor_get(v_v_1119_, 0);
v_val_1129_ = lean_ctor_get(v_v_1119_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_v_1119_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1131_ = v_v_1119_;
v_isShared_1132_ = v_isSharedCheck_1139_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_val_1129_);
lean_inc(v_key_1128_);
lean_dec(v_v_1119_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1139_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
uint8_t v___x_1133_; 
v___x_1133_ = l_Lean_instBEqFVarId_beq(v_x_1108_, v_key_1128_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_del_object(v___x_1131_);
v___x_1134_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1128_, v_val_1129_, v_x_1108_, v_x_1109_);
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
v___y_1123_ = v___x_1135_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1137_; 
lean_dec(v_val_1129_);
lean_dec(v_key_1128_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v_x_1109_);
lean_ctor_set(v___x_1131_, 0, v_x_1108_);
v___x_1137_ = v___x_1131_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_x_1108_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_x_1109_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
v___y_1123_ = v___x_1137_;
goto v___jp_1122_;
}
}
}
}
case 1:
{
lean_object* v_node_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1152_; 
v_node_1140_ = lean_ctor_get(v_v_1119_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_v_1119_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1142_ = v_v_1119_;
v_isShared_1143_ = v_isSharedCheck_1152_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_node_1140_);
lean_dec(v_v_1119_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1152_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
size_t v___x_1144_; size_t v___x_1145_; size_t v___x_1146_; size_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1144_ = ((size_t)5ULL);
v___x_1145_ = lean_usize_shift_right(v_x_1106_, v___x_1144_);
v___x_1146_ = ((size_t)1ULL);
v___x_1147_ = lean_usize_add(v_x_1107_, v___x_1146_);
v___x_1148_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_node_1140_, v___x_1145_, v___x_1147_, v_x_1108_, v_x_1109_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1148_);
v___x_1150_ = v___x_1142_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
v___y_1123_ = v___x_1150_;
goto v___jp_1122_;
}
}
}
default: 
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_x_1108_);
lean_ctor_set(v___x_1153_, 1, v_x_1109_);
v___y_1123_ = v___x_1153_;
goto v___jp_1122_;
}
}
v___jp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_array_fset(v_xs_x27_1121_, v_j_1113_, v___y_1123_);
lean_dec(v_j_1113_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1124_);
v___x_1126_ = v___x_1117_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
else
{
lean_object* v_ks_1156_; lean_object* v_vs_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1177_; 
v_ks_1156_ = lean_ctor_get(v_x_1105_, 0);
v_vs_1157_ = lean_ctor_get(v_x_1105_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_x_1105_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1159_ = v_x_1105_;
v_isShared_1160_ = v_isSharedCheck_1177_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_vs_1157_);
lean_inc(v_ks_1156_);
lean_dec(v_x_1105_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1177_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_ks_1156_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_vs_1157_);
v___x_1162_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v_newNode_1163_; uint8_t v___y_1165_; size_t v___x_1171_; uint8_t v___x_1172_; 
v_newNode_1163_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__15___redArg(v___x_1162_, v_x_1108_, v_x_1109_);
v___x_1171_ = ((size_t)7ULL);
v___x_1172_ = lean_usize_dec_le(v___x_1171_, v_x_1107_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1173_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1163_);
v___x_1174_ = lean_unsigned_to_nat(4u);
v___x_1175_ = lean_nat_dec_lt(v___x_1173_, v___x_1174_);
lean_dec(v___x_1173_);
v___y_1165_ = v___x_1175_;
goto v___jp_1164_;
}
else
{
v___y_1165_ = v___x_1172_;
goto v___jp_1164_;
}
v___jp_1164_:
{
if (v___y_1165_ == 0)
{
lean_object* v_ks_1166_; lean_object* v_vs_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_ks_1166_ = lean_ctor_get(v_newNode_1163_, 0);
lean_inc_ref(v_ks_1166_);
v_vs_1167_ = lean_ctor_get(v_newNode_1163_, 1);
lean_inc_ref(v_vs_1167_);
lean_dec_ref(v_newNode_1163_);
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___closed__0);
v___x_1170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__16___redArg(v_x_1107_, v_ks_1166_, v_vs_1167_, v___x_1168_, v___x_1169_);
lean_dec_ref(v_vs_1167_);
lean_dec_ref(v_ks_1166_);
return v___x_1170_;
}
else
{
return v_newNode_1163_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__16___redArg(size_t v_depth_1178_, lean_object* v_keys_1179_, lean_object* v_vals_1180_, lean_object* v_i_1181_, lean_object* v_entries_1182_){
_start:
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_array_get_size(v_keys_1179_);
v___x_1184_ = lean_nat_dec_lt(v_i_1181_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_dec(v_i_1181_);
return v_entries_1182_;
}
else
{
lean_object* v_k_1185_; lean_object* v_v_1186_; uint64_t v___x_1187_; size_t v_h_1188_; size_t v___x_1189_; lean_object* v___x_1190_; size_t v___x_1191_; size_t v___x_1192_; size_t v___x_1193_; size_t v_h_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_k_1185_ = lean_array_fget_borrowed(v_keys_1179_, v_i_1181_);
v_v_1186_ = lean_array_fget_borrowed(v_vals_1180_, v_i_1181_);
v___x_1187_ = l_Lean_instHashableFVarId_hash(v_k_1185_);
v_h_1188_ = lean_uint64_to_usize(v___x_1187_);
v___x_1189_ = ((size_t)5ULL);
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = ((size_t)1ULL);
v___x_1192_ = lean_usize_sub(v_depth_1178_, v___x_1191_);
v___x_1193_ = lean_usize_mul(v___x_1189_, v___x_1192_);
v_h_1194_ = lean_usize_shift_right(v_h_1188_, v___x_1193_);
v___x_1195_ = lean_nat_add(v_i_1181_, v___x_1190_);
lean_dec(v_i_1181_);
lean_inc(v_v_1186_);
lean_inc(v_k_1185_);
v___x_1196_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_entries_1182_, v_h_1194_, v_depth_1178_, v_k_1185_, v_v_1186_);
v_i_1181_ = v___x_1195_;
v_entries_1182_ = v___x_1196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_depth_1198_, lean_object* v_keys_1199_, lean_object* v_vals_1200_, lean_object* v_i_1201_, lean_object* v_entries_1202_){
_start:
{
size_t v_depth_boxed_1203_; lean_object* v_res_1204_; 
v_depth_boxed_1203_ = lean_unbox_usize(v_depth_1198_);
lean_dec(v_depth_1198_);
v_res_1204_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__16___redArg(v_depth_boxed_1203_, v_keys_1199_, v_vals_1200_, v_i_1201_, v_entries_1202_);
lean_dec_ref(v_vals_1200_);
lean_dec_ref(v_keys_1199_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___boxed(lean_object* v_x_1205_, lean_object* v_x_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_){
_start:
{
size_t v_x_34186__boxed_1210_; size_t v_x_34187__boxed_1211_; lean_object* v_res_1212_; 
v_x_34186__boxed_1210_ = lean_unbox_usize(v_x_1206_);
lean_dec(v_x_1206_);
v_x_34187__boxed_1211_ = lean_unbox_usize(v_x_1207_);
lean_dec(v_x_1207_);
v_res_1212_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_x_1205_, v_x_34186__boxed_1210_, v_x_34187__boxed_1211_, v_x_1208_, v_x_1209_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(lean_object* v_x_1213_, lean_object* v_x_1214_, lean_object* v_x_1215_){
_start:
{
uint64_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; 
v___x_1216_ = l_Lean_instHashableFVarId_hash(v_x_1214_);
v___x_1217_ = lean_uint64_to_usize(v___x_1216_);
v___x_1218_ = ((size_t)1ULL);
v___x_1219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_x_1213_, v___x_1217_, v___x_1218_, v_x_1214_, v_x_1215_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object* v_e_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
uint8_t v_a_boxed_1229_; lean_object* v_res_1230_; 
v_a_boxed_1229_ = lean_unbox(v_a_1222_);
v_res_1230_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1221_, v_a_boxed_1229_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object* v_as_1231_, size_t v_sz_1232_, size_t v_i_1233_, lean_object* v_b_1234_, uint8_t v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_a_1243_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; uint8_t v___x_1256_; 
v___x_1256_ = lean_usize_dec_lt(v_i_1233_, v_sz_1232_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_b_1234_);
return v___x_1257_;
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1259_; lean_object* v_localDecl_1261_; lean_object* v___x_1269_; 
v_a_1258_ = lean_array_uget_borrowed(v_as_1231_, v_i_1233_);
v___x_1259_ = l_Lean_Expr_fvarId_x21(v_a_1258_);
lean_inc(v___x_1259_);
v___x_1269_ = l_Lean_FVarId_getDecl___redArg(v___x_1259_, v___y_1237_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = l_Lean_LocalDecl_type(v_a_1270_);
v___x_1272_ = l_Lean_Meta_AbstractNestedProofs_visit(v___x_1271_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = l_Lean_LocalDecl_setType(v_a_1270_, v_a_1273_);
v___x_1275_ = l_Lean_LocalDecl_value_x3f(v___x_1274_, v___x_1256_);
if (lean_obj_tag(v___x_1275_) == 0)
{
v_localDecl_1261_ = v___x_1274_;
goto v___jp_1260_;
}
else
{
lean_object* v_val_1276_; lean_object* v___x_1277_; 
v_val_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_val_1276_);
lean_dec_ref_known(v___x_1275_, 1);
v___x_1277_ = l_Lean_Meta_AbstractNestedProofs_visit(v_val_1276_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = l_Lean_LocalDecl_setValue(v___x_1274_, v_a_1278_);
v_localDecl_1261_ = v___x_1279_;
goto v___jp_1260_;
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v___x_1274_);
lean_dec(v___x_1259_);
lean_dec_ref(v_b_1234_);
v_a_1280_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1277_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1277_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_a_1270_);
lean_dec(v___x_1259_);
lean_dec_ref(v_b_1234_);
v_a_1288_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1272_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1272_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v___x_1259_);
lean_dec_ref(v_b_1234_);
v_a_1296_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1269_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1269_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
v___jp_1260_:
{
lean_object* v_fvarIdToDecl_1262_; lean_object* v_decls_1263_; lean_object* v_auxDeclToFullName_1264_; lean_object* v___x_1265_; 
v_fvarIdToDecl_1262_ = lean_ctor_get(v_b_1234_, 0);
v_decls_1263_ = lean_ctor_get(v_b_1234_, 1);
v_auxDeclToFullName_1264_ = lean_ctor_get(v_b_1234_, 2);
lean_inc_ref(v_b_1234_);
v___x_1265_ = lean_local_ctx_find(v_b_1234_, v___x_1259_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_dec_ref(v_localDecl_1261_);
v_a_1243_ = v_b_1234_;
goto v___jp_1242_;
}
else
{
lean_object* v_index_1266_; lean_object* v_fvarId_1267_; lean_object* v___x_1268_; 
lean_inc(v_auxDeclToFullName_1264_);
lean_inc_ref(v_decls_1263_);
lean_inc_ref(v_fvarIdToDecl_1262_);
lean_dec_ref_known(v___x_1265_, 1);
lean_dec_ref(v_b_1234_);
v_index_1266_ = lean_ctor_get(v_localDecl_1261_, 0);
lean_inc(v_index_1266_);
v_fvarId_1267_ = lean_ctor_get(v_localDecl_1261_, 1);
lean_inc_ref(v_localDecl_1261_);
lean_inc(v_fvarId_1267_);
v___x_1268_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_fvarIdToDecl_1262_, v_fvarId_1267_, v_localDecl_1261_);
v___y_1248_ = v_decls_1263_;
v___y_1249_ = v_auxDeclToFullName_1264_;
v___y_1250_ = v_localDecl_1261_;
v___y_1251_ = v___x_1268_;
v___y_1252_ = v_index_1266_;
goto v___jp_1247_;
}
}
}
v___jp_1242_:
{
size_t v___x_1244_; size_t v___x_1245_; 
v___x_1244_ = ((size_t)1ULL);
v___x_1245_ = lean_usize_add(v_i_1233_, v___x_1244_);
v_i_1233_ = v___x_1245_;
v_b_1234_ = v_a_1243_;
goto _start;
}
v___jp_1247_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___y_1250_);
v___x_1254_ = l_Lean_PersistentArray_set___redArg(v___y_1248_, v___y_1252_, v___x_1253_);
lean_dec(v___y_1252_);
v___x_1255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1255_, 0, v___y_1251_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
lean_ctor_set(v___x_1255_, 2, v___y_1249_);
v_a_1243_ = v___x_1255_;
goto v___jp_1242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object* v_xs_1304_, lean_object* v_k_1305_, uint8_t v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_lctx_1313_; lean_object* v_localInstances_1314_; size_t v_sz_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v_lctx_1313_ = lean_ctor_get(v___y_1308_, 2);
v_localInstances_1314_ = lean_ctor_get(v___y_1308_, 3);
v_sz_1315_ = lean_array_size(v_xs_1304_);
v___x_1316_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1313_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_xs_1304_, v_sz_1315_, v___x_1316_, v_lctx_1313_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1319_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
lean_inc_ref(v_localInstances_1314_);
v___x_1319_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_a_1318_, v_localInstances_1314_, v_k_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
return v___x_1319_;
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v_k_1305_);
v_a_1320_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1317_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1317_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object* v_xs_1328_, lean_object* v_k_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v___y_34407__boxed_1337_; lean_object* v_res_1338_; 
v___y_34407__boxed_1337_ = lean_unbox(v___y_1330_);
v_res_1338_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(v_xs_1328_, v_k_1329_, v___y_34407__boxed_1337_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v_xs_1328_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object* v___y_1339_, lean_object* v___f_1340_, lean_object* v_xs_1341_, lean_object* v_b_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
uint8_t v___y_34357__boxed_1350_; uint8_t v___y_34359__boxed_1351_; lean_object* v_res_1352_; 
v___y_34357__boxed_1350_ = lean_unbox(v___y_1339_);
v___y_34359__boxed_1351_ = lean_unbox(v___y_1343_);
v_res_1352_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(v___y_34357__boxed_1350_, v___f_1340_, v_xs_1341_, v_b_1342_, v___y_34359__boxed_1351_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object* v_b_1353_, lean_object* v_xs_1354_, uint8_t v___y_1355_, uint8_t v___x_1356_, uint8_t v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1353_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; uint8_t v___x_1366_; lean_object* v___x_1367_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = 1;
v___x_1367_ = l_Lean_Meta_mkForallFVars(v_xs_1354_, v_a_1365_, v___y_1355_, v___x_1356_, v___x_1356_, v___x_1366_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
return v___x_1367_;
}
else
{
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object* v_b_1368_, lean_object* v_xs_1369_, lean_object* v___y_1370_, lean_object* v___x_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
uint8_t v___y_34393__boxed_1379_; uint8_t v___x_34394__boxed_1380_; uint8_t v___y_34395__boxed_1381_; lean_object* v_res_1382_; 
v___y_34393__boxed_1379_ = lean_unbox(v___y_1370_);
v___x_34394__boxed_1380_ = lean_unbox(v___x_1371_);
v___y_34395__boxed_1381_ = lean_unbox(v___y_1372_);
v_res_1382_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(v_b_1368_, v_xs_1369_, v___y_34393__boxed_1379_, v___x_34394__boxed_1380_, v___y_34395__boxed_1381_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v_xs_1369_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t v___y_1383_, uint8_t v___x_1384_, lean_object* v___f_1385_, lean_object* v_xs_1386_, lean_object* v_b_1387_, uint8_t v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___f_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1395_ = lean_box(v___y_1383_);
v___x_1396_ = lean_box(v___x_1384_);
lean_inc_ref(v_xs_1386_);
v___f_1397_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1397_, 0, v_b_1387_);
lean_closure_set(v___f_1397_, 1, v_xs_1386_);
lean_closure_set(v___f_1397_, 2, v___x_1395_);
lean_closure_set(v___f_1397_, 3, v___x_1396_);
v___x_1398_ = lean_box(v___y_1388_);
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc_ref(v___y_1390_);
lean_inc(v___y_1389_);
v___x_1399_ = lean_apply_9(v___f_1385_, v_xs_1386_, v___f_1397_, v___x_1398_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, lean_box(0));
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object* v___y_1400_, lean_object* v___x_1401_, lean_object* v___f_1402_, lean_object* v_xs_1403_, lean_object* v_b_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v___y_34368__boxed_1412_; uint8_t v___x_34369__boxed_1413_; uint8_t v___y_34371__boxed_1414_; lean_object* v_res_1415_; 
v___y_34368__boxed_1412_ = lean_unbox(v___y_1400_);
v___x_34369__boxed_1413_ = lean_unbox(v___x_1401_);
v___y_34371__boxed_1414_ = lean_unbox(v___y_1405_);
v_res_1415_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(v___y_34368__boxed_1412_, v___x_34369__boxed_1413_, v___f_1402_, v_xs_1403_, v_b_1404_, v___y_34371__boxed_1414_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t v_sz_1416_, size_t v_i_1417_, lean_object* v_bs_1418_, uint8_t v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
uint8_t v___x_1426_; 
v___x_1426_ = lean_usize_dec_lt(v_i_1417_, v_sz_1416_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_bs_1418_);
return v___x_1427_;
}
else
{
lean_object* v_v_1428_; lean_object* v___x_1429_; 
v_v_1428_ = lean_array_uget_borrowed(v_bs_1418_, v_i_1417_);
lean_inc(v_v_1428_);
v___x_1429_ = l_Lean_Meta_AbstractNestedProofs_visit(v_v_1428_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; lean_object* v_bs_x27_1432_; size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = lean_unsigned_to_nat(0u);
v_bs_x27_1432_ = lean_array_uset(v_bs_1418_, v_i_1417_, v___x_1431_);
v___x_1433_ = ((size_t)1ULL);
v___x_1434_ = lean_usize_add(v_i_1417_, v___x_1433_);
v___x_1435_ = lean_array_uset(v_bs_x27_1432_, v_i_1417_, v_a_1430_);
v_i_1417_ = v___x_1434_;
v_bs_1418_ = v___x_1435_;
goto _start;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v_bs_1418_);
v_a_1437_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1429_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1429_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__10(lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_, uint8_t v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
if (lean_obj_tag(v_x_1445_) == 5)
{
lean_object* v_fn_1455_; lean_object* v_arg_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_fn_1455_ = lean_ctor_get(v_x_1445_, 0);
lean_inc_ref(v_fn_1455_);
v_arg_1456_ = lean_ctor_get(v_x_1445_, 1);
lean_inc_ref(v_arg_1456_);
lean_dec_ref_known(v_x_1445_, 2);
v___x_1457_ = lean_array_set(v_x_1446_, v_x_1447_, v_arg_1456_);
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1459_ = lean_nat_sub(v_x_1447_, v___x_1458_);
lean_dec(v_x_1447_);
v_x_1445_ = v_fn_1455_;
v_x_1446_ = v___x_1457_;
v_x_1447_ = v___x_1459_;
goto _start;
}
else
{
lean_object* v___x_1461_; 
lean_dec(v_x_1447_);
v___x_1461_ = l_Lean_Meta_AbstractNestedProofs_visit(v_x_1445_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; size_t v_sz_1463_; size_t v___x_1464_; lean_object* v___x_1465_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v_sz_1463_ = lean_array_size(v_x_1446_);
v___x_1464_ = ((size_t)0ULL);
v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_1463_, v___x_1464_, v_x_1446_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1474_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = l_Lean_mkAppN(v_a_1462_, v_a_1466_);
lean_dec(v_a_1466_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v_a_1462_);
v_a_1475_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1465_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1465_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
else
{
lean_dec_ref(v_x_1446_);
return v___x_1461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object* v_e_1483_, uint8_t v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v_i_1499_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v_i_1518_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v_a_1536_; lean_object* v___y_1569_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_visit___closed__0));
v___x_1572_ = l_Lean_Core_checkSystem(v___x_1571_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1639_; 
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1639_ == 0)
{
lean_object* v_unused_1640_; 
v_unused_1640_ = lean_ctor_get(v___x_1572_, 0);
lean_dec(v_unused_1640_);
v___x_1574_ = v___x_1572_;
v_isShared_1575_ = v_isSharedCheck_1639_;
goto v_resetjp_1573_;
}
else
{
lean_dec(v___x_1572_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1639_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
uint8_t v___x_1576_; 
v___x_1576_ = l_Lean_Expr_isAtomic(v_e_1483_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_st_ref_get(v_a_1485_);
v___x_1578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v___x_1577_, v_e_1483_);
lean_dec(v___x_1577_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1579_; 
lean_del_object(v___x_1574_);
lean_inc_ref(v_e_1483_);
v___x_1579_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_1483_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___f_1584_; uint8_t v___x_1585_; uint8_t v___y_1587_; uint8_t v___x_1621_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___f_1584_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed), 9, 0);
v___x_1585_ = 1;
v___x_1621_ = lean_unbox(v_a_1580_);
if (v___x_1621_ == 0)
{
uint8_t v___x_1622_; 
v___x_1622_ = lean_unbox(v_a_1580_);
lean_dec(v_a_1580_);
v___y_1587_ = v___x_1622_;
goto v___jp_1586_;
}
else
{
uint8_t v___x_1623_; 
lean_dec(v_a_1580_);
v___x_1623_ = l_Lean_Expr_hasSorry(v_e_1483_);
if (v___x_1623_ == 0)
{
lean_dec_ref(v___f_1584_);
goto v___jp_1581_;
}
else
{
if (v___x_1576_ == 0)
{
v___y_1587_ = v___x_1576_;
goto v___jp_1586_;
}
else
{
lean_dec_ref(v___f_1584_);
goto v___jp_1581_;
}
}
}
v___jp_1581_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___boxed), 8, 0);
lean_inc_ref(v_e_1483_);
v___x_1583_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(v_e_1483_, v_a_1484_, v___x_1582_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
v___y_1569_ = v___x_1583_;
goto v___jp_1568_;
}
v___jp_1586_:
{
switch(lean_obj_tag(v_e_1483_))
{
case 6:
{
lean_object* v___x_1588_; lean_object* v___f_1589_; lean_object* v___x_1590_; 
v___x_1588_ = lean_box(v___y_1587_);
v___f_1589_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1589_, 0, v___x_1588_);
lean_closure_set(v___f_1589_, 1, v___f_1584_);
lean_inc_ref(v_e_1483_);
v___x_1590_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_e_1483_, v___f_1589_, v___y_1587_, v___x_1585_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
v___y_1569_ = v___x_1590_;
goto v___jp_1568_;
}
case 8:
{
lean_object* v___x_1591_; lean_object* v___f_1592_; lean_object* v___x_1593_; 
v___x_1591_ = lean_box(v___y_1587_);
v___f_1592_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1592_, 0, v___x_1591_);
lean_closure_set(v___f_1592_, 1, v___f_1584_);
lean_inc_ref(v_e_1483_);
v___x_1593_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_e_1483_, v___f_1592_, v___y_1587_, v___x_1585_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
v___y_1569_ = v___x_1593_;
goto v___jp_1568_;
}
case 7:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___f_1596_; lean_object* v___x_1597_; 
v___x_1594_ = lean_box(v___y_1587_);
v___x_1595_ = lean_box(v___x_1585_);
v___f_1596_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed), 12, 3);
lean_closure_set(v___f_1596_, 0, v___x_1594_);
lean_closure_set(v___f_1596_, 1, v___x_1595_);
lean_closure_set(v___f_1596_, 2, v___f_1584_);
lean_inc_ref(v_e_1483_);
v___x_1597_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___redArg(v_e_1483_, v___f_1596_, v___y_1587_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
v___y_1569_ = v___x_1597_;
goto v___jp_1568_;
}
case 10:
{
lean_object* v_data_1598_; lean_object* v_expr_1599_; lean_object* v___x_1600_; 
lean_dec_ref(v___f_1584_);
v_data_1598_ = lean_ctor_get(v_e_1483_, 0);
v_expr_1599_ = lean_ctor_get(v_e_1483_, 1);
lean_inc_ref(v_expr_1599_);
v___x_1600_ = l_Lean_Meta_AbstractNestedProofs_visit(v_expr_1599_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; size_t v___x_1602_; size_t v___x_1603_; uint8_t v___x_1604_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
v___x_1602_ = lean_ptr_addr(v_expr_1599_);
v___x_1603_ = lean_ptr_addr(v_a_1601_);
v___x_1604_ = lean_usize_dec_eq(v___x_1602_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; 
lean_inc(v_data_1598_);
v___x_1605_ = l_Lean_Expr_mdata___override(v_data_1598_, v_a_1601_);
v_a_1536_ = v___x_1605_;
goto v___jp_1535_;
}
else
{
lean_dec(v_a_1601_);
lean_inc_ref(v_e_1483_);
v_a_1536_ = v_e_1483_;
goto v___jp_1535_;
}
}
else
{
v___y_1569_ = v___x_1600_;
goto v___jp_1568_;
}
}
case 11:
{
lean_object* v_typeName_1606_; lean_object* v_idx_1607_; lean_object* v_struct_1608_; lean_object* v___x_1609_; 
lean_dec_ref(v___f_1584_);
v_typeName_1606_ = lean_ctor_get(v_e_1483_, 0);
v_idx_1607_ = lean_ctor_get(v_e_1483_, 1);
v_struct_1608_ = lean_ctor_get(v_e_1483_, 2);
lean_inc_ref(v_struct_1608_);
v___x_1609_ = l_Lean_Meta_AbstractNestedProofs_visit(v_struct_1608_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; size_t v___x_1611_; size_t v___x_1612_; uint8_t v___x_1613_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1611_ = lean_ptr_addr(v_struct_1608_);
v___x_1612_ = lean_ptr_addr(v_a_1610_);
v___x_1613_ = lean_usize_dec_eq(v___x_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_inc(v_idx_1607_);
lean_inc(v_typeName_1606_);
v___x_1614_ = l_Lean_Expr_proj___override(v_typeName_1606_, v_idx_1607_, v_a_1610_);
v_a_1536_ = v___x_1614_;
goto v___jp_1535_;
}
else
{
lean_dec(v_a_1610_);
lean_inc_ref(v_e_1483_);
v_a_1536_ = v_e_1483_;
goto v___jp_1535_;
}
}
else
{
v___y_1569_ = v___x_1609_;
goto v___jp_1568_;
}
}
case 5:
{
lean_object* v_dummy_1615_; lean_object* v_nargs_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_dec_ref(v___f_1584_);
v_dummy_1615_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_1616_ = l_Lean_Expr_getAppNumArgs(v_e_1483_);
lean_inc(v_nargs_1616_);
v___x_1617_ = lean_mk_array(v_nargs_1616_, v_dummy_1615_);
v___x_1618_ = lean_unsigned_to_nat(1u);
v___x_1619_ = lean_nat_sub(v_nargs_1616_, v___x_1618_);
lean_dec(v_nargs_1616_);
lean_inc_ref(v_e_1483_);
v___x_1620_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__10(v_e_1483_, v___x_1617_, v___x_1619_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
v___y_1569_ = v___x_1620_;
goto v___jp_1568_;
}
default: 
{
lean_dec_ref(v___f_1584_);
lean_inc_ref(v_e_1483_);
v_a_1536_ = v_e_1483_;
goto v___jp_1535_;
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_e_1483_);
v_a_1624_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1579_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1579_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v_val_1632_; lean_object* v___x_1634_; 
lean_dec_ref(v_e_1483_);
v_val_1632_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_val_1632_);
lean_dec_ref_known(v___x_1578_, 1);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v_val_1632_);
v___x_1634_ = v___x_1574_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_val_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
else
{
lean_object* v___x_1637_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v_e_1483_);
v___x_1637_ = v___x_1574_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_e_1483_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v_e_1483_);
v_a_1641_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1572_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1572_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
v___jp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_st_ref_put(v_a_1485_, v___y_1493_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___y_1492_);
return v___x_1495_;
}
v___jp_1496_:
{
lean_object* v_size_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v_size_1500_ = lean_ctor_get(v___y_1498_, 0);
v___x_1501_ = lean_unsigned_to_nat(1u);
v___x_1502_ = lean_nat_add(v_size_1500_, v___x_1501_);
lean_inc_ref(v___y_1497_);
v___x_1503_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1498_, v___x_1502_, v_i_1499_, v_e_1483_, v___y_1497_);
lean_dec(v_i_1499_);
v___y_1492_ = v___y_1497_;
v___y_1493_ = v___x_1503_;
goto v___jp_1491_;
}
v___jp_1504_:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v___y_1506_, v_e_1483_);
switch(lean_obj_tag(v___x_1507_))
{
case 0:
{
lean_object* v_index_1508_; lean_object* v_size_1509_; lean_object* v___x_1510_; 
v_index_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_index_1508_);
lean_dec_ref_known(v___x_1507_, 3);
v_size_1509_ = lean_ctor_get(v___y_1506_, 0);
lean_inc(v_size_1509_);
lean_inc_ref(v___y_1505_);
v___x_1510_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1506_, v_size_1509_, v_index_1508_, v_e_1483_, v___y_1505_);
lean_dec(v_index_1508_);
v___y_1492_ = v___y_1505_;
v___y_1493_ = v___x_1510_;
goto v___jp_1491_;
}
case 1:
{
lean_object* v_index_1511_; 
v_index_1511_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_index_1511_);
lean_dec_ref_known(v___x_1507_, 1);
v___y_1497_ = v___y_1505_;
v___y_1498_ = v___y_1506_;
v_i_1499_ = v_index_1511_;
goto v___jp_1496_;
}
default: 
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1506_, v___x_1512_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_index_1514_; 
v_index_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_index_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___y_1497_ = v___y_1505_;
v___y_1498_ = v___y_1506_;
v_i_1499_ = v_index_1514_;
goto v___jp_1496_;
}
else
{
lean_dec_ref(v_e_1483_);
v___y_1492_ = v___y_1505_;
v___y_1493_ = v___y_1506_;
goto v___jp_1491_;
}
}
}
}
v___jp_1515_:
{
lean_object* v_size_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_size_1519_ = lean_ctor_get(v___y_1516_, 0);
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = lean_nat_add(v_size_1519_, v___x_1520_);
lean_inc_ref(v___y_1517_);
v___x_1522_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1516_, v___x_1521_, v_i_1518_, v_e_1483_, v___y_1517_);
lean_dec(v_i_1518_);
v___y_1492_ = v___y_1517_;
v___y_1493_ = v___x_1522_;
goto v___jp_1491_;
}
v___jp_1523_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v___y_1524_);
lean_dec_ref(v___y_1524_);
v___x_1527_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v___x_1526_, v_e_1483_);
switch(lean_obj_tag(v___x_1527_))
{
case 0:
{
lean_object* v_index_1528_; lean_object* v_size_1529_; lean_object* v___x_1530_; 
v_index_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_index_1528_);
lean_dec_ref_known(v___x_1527_, 3);
v_size_1529_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_size_1529_);
lean_inc_ref(v___y_1525_);
v___x_1530_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1526_, v_size_1529_, v_index_1528_, v_e_1483_, v___y_1525_);
lean_dec(v_index_1528_);
v___y_1492_ = v___y_1525_;
v___y_1493_ = v___x_1530_;
goto v___jp_1491_;
}
case 1:
{
lean_object* v_index_1531_; 
v_index_1531_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_index_1531_);
lean_dec_ref_known(v___x_1527_, 1);
v___y_1516_ = v___x_1526_;
v___y_1517_ = v___y_1525_;
v_i_1518_ = v_index_1531_;
goto v___jp_1515_;
}
default: 
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1526_, v___x_1532_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_index_1534_; 
v_index_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_index_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___y_1516_ = v___x_1526_;
v___y_1517_ = v___y_1525_;
v_i_1518_ = v_index_1534_;
goto v___jp_1515_;
}
else
{
lean_dec_ref(v_e_1483_);
v___y_1492_ = v___y_1525_;
v___y_1493_ = v___x_1526_;
goto v___jp_1491_;
}
}
}
}
v___jp_1535_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_st_ref_take(v_a_1485_);
v___x_1538_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v___x_1537_, v_e_1483_);
switch(lean_obj_tag(v___x_1538_))
{
case 0:
{
lean_object* v_index_1539_; lean_object* v_size_1540_; lean_object* v___x_1541_; 
v_index_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_index_1539_);
lean_dec_ref_known(v___x_1538_, 3);
v_size_1540_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_size_1540_);
lean_inc_ref(v_a_1536_);
v___x_1541_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1537_, v_size_1540_, v_index_1539_, v_e_1483_, v_a_1536_);
lean_dec(v_index_1539_);
v___y_1492_ = v_a_1536_;
v___y_1493_ = v___x_1541_;
goto v___jp_1491_;
}
case 1:
{
lean_object* v_index_1542_; lean_object* v_size_1543_; lean_object* v_keyArray_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_index_1542_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_index_1542_);
lean_dec_ref_known(v___x_1538_, 1);
v_size_1543_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_size_1543_);
v_keyArray_1544_ = lean_ctor_get(v___x_1537_, 1);
lean_inc_ref(v_keyArray_1544_);
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = lean_nat_add(v_size_1543_, v___x_1545_);
lean_dec(v_size_1543_);
v___x_1547_ = lean_array_get_size(v_keyArray_1544_);
lean_dec_ref(v_keyArray_1544_);
v___x_1548_ = lean_nat_dec_lt(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_dec(v___x_1546_);
lean_dec(v_index_1542_);
v___y_1524_ = v___x_1537_;
v___y_1525_ = v_a_1536_;
goto v___jp_1523_;
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1549_ = lean_unsigned_to_nat(4u);
v___x_1550_ = lean_nat_mul(v___x_1546_, v___x_1549_);
v___x_1551_ = lean_unsigned_to_nat(3u);
v___x_1552_ = lean_nat_mul(v___x_1547_, v___x_1551_);
v___x_1553_ = lean_nat_dec_le(v___x_1550_, v___x_1552_);
lean_dec(v___x_1552_);
lean_dec(v___x_1550_);
if (v___x_1553_ == 0)
{
lean_dec(v___x_1546_);
lean_dec(v_index_1542_);
v___y_1524_ = v___x_1537_;
v___y_1525_ = v_a_1536_;
goto v___jp_1523_;
}
else
{
lean_object* v___x_1554_; 
lean_inc_ref(v_a_1536_);
v___x_1554_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1537_, v___x_1546_, v_index_1542_, v_e_1483_, v_a_1536_);
lean_dec(v_index_1542_);
v___y_1492_ = v_a_1536_;
v___y_1493_ = v___x_1554_;
goto v___jp_1491_;
}
}
}
default: 
{
lean_object* v_size_1555_; lean_object* v_keyArray_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_size_1555_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_size_1555_);
v_keyArray_1556_ = lean_ctor_get(v___x_1537_, 1);
lean_inc_ref(v_keyArray_1556_);
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = lean_nat_add(v_size_1555_, v___x_1557_);
lean_dec(v_size_1555_);
v___x_1559_ = lean_array_get_size(v_keyArray_1556_);
lean_dec_ref(v_keyArray_1556_);
v___x_1560_ = lean_nat_dec_lt(v___x_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
lean_dec(v___x_1558_);
v___x_1561_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v___x_1537_);
lean_dec(v___x_1537_);
v___y_1505_ = v_a_1536_;
v___y_1506_ = v___x_1561_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1562_ = lean_unsigned_to_nat(4u);
v___x_1563_ = lean_nat_mul(v___x_1558_, v___x_1562_);
lean_dec(v___x_1558_);
v___x_1564_ = lean_unsigned_to_nat(3u);
v___x_1565_ = lean_nat_mul(v___x_1559_, v___x_1564_);
v___x_1566_ = lean_nat_dec_le(v___x_1563_, v___x_1565_);
lean_dec(v___x_1565_);
lean_dec(v___x_1563_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v___x_1537_);
lean_dec(v___x_1537_);
v___y_1505_ = v_a_1536_;
v___y_1506_ = v___x_1567_;
goto v___jp_1504_;
}
else
{
v___y_1505_ = v_a_1536_;
v___y_1506_ = v___x_1537_;
goto v___jp_1504_;
}
}
}
}
}
v___jp_1568_:
{
if (lean_obj_tag(v___y_1569_) == 0)
{
lean_object* v_a_1570_; 
v_a_1570_ = lean_ctor_get(v___y_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___y_1569_, 1);
v_a_1536_ = v_a_1570_;
goto v___jp_1535_;
}
else
{
lean_dec_ref(v_e_1483_);
return v___y_1569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object* v_b_1649_, lean_object* v_xs_1650_, uint8_t v___y_1651_, uint8_t v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1649_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v___x_1661_ = 1;
v___x_1662_ = l_Lean_Meta_mkLambdaFVars(v_xs_1650_, v_a_1660_, v___y_1651_, v___y_1651_, v___y_1651_, v___y_1651_, v___x_1661_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
return v___x_1662_;
}
else
{
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object* v_b_1663_, lean_object* v_xs_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
uint8_t v___y_34380__boxed_1673_; uint8_t v___y_34381__boxed_1674_; lean_object* v_res_1675_; 
v___y_34380__boxed_1673_ = lean_unbox(v___y_1665_);
v___y_34381__boxed_1674_ = lean_unbox(v___y_1666_);
v_res_1675_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(v_b_1663_, v_xs_1664_, v___y_34380__boxed_1673_, v___y_34381__boxed_1674_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v_xs_1664_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t v___y_1676_, lean_object* v___f_1677_, lean_object* v_xs_1678_, lean_object* v_b_1679_, uint8_t v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; lean_object* v___f_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1687_ = lean_box(v___y_1676_);
lean_inc_ref(v_xs_1678_);
v___f_1688_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1688_, 0, v_b_1679_);
lean_closure_set(v___f_1688_, 1, v_xs_1678_);
lean_closure_set(v___f_1688_, 2, v___x_1687_);
v___x_1689_ = lean_box(v___y_1680_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1681_);
v___x_1690_ = lean_apply_9(v___f_1677_, v_xs_1678_, v___f_1688_, v___x_1689_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, lean_box(0));
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object* v_sz_1691_, lean_object* v_i_1692_, lean_object* v_bs_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
size_t v_sz_boxed_1701_; size_t v_i_boxed_1702_; uint8_t v___y_34420__boxed_1703_; lean_object* v_res_1704_; 
v_sz_boxed_1701_ = lean_unbox_usize(v_sz_1691_);
lean_dec(v_sz_1691_);
v_i_boxed_1702_ = lean_unbox_usize(v_i_1692_);
lean_dec(v_i_1692_);
v___y_34420__boxed_1703_ = lean_unbox(v___y_1694_);
v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_boxed_1701_, v_i_boxed_1702_, v_bs_1693_, v___y_34420__boxed_1703_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__10___boxed(lean_object* v_x_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v___y_34441__boxed_1715_; lean_object* v_res_1716_; 
v___y_34441__boxed_1715_ = lean_unbox(v___y_1708_);
v_res_1716_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__10(v_x_1705_, v_x_1706_, v_x_1707_, v___y_34441__boxed_1715_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object* v_as_1717_, lean_object* v_sz_1718_, lean_object* v_i_1719_, lean_object* v_b_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
size_t v_sz_boxed_1728_; size_t v_i_boxed_1729_; uint8_t v___y_34464__boxed_1730_; lean_object* v_res_1731_; 
v_sz_boxed_1728_ = lean_unbox_usize(v_sz_1718_);
lean_dec(v_sz_1718_);
v_i_boxed_1729_ = lean_unbox_usize(v_i_1719_);
lean_dec(v_i_1719_);
v___y_34464__boxed_1730_ = lean_unbox(v___y_1721_);
v_res_1731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_as_1717_, v_sz_boxed_1728_, v_i_boxed_1729_, v_b_1720_, v___y_34464__boxed_1730_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v_as_1717_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object* v_00_u03b2_1732_, lean_object* v_m_1733_, lean_object* v_query_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_m_1733_, v_query_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___boxed(lean_object* v_00_u03b2_1736_, lean_object* v_m_1737_, lean_object* v_query_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(v_00_u03b2_1736_, v_m_1737_, v_query_1738_);
lean_dec_ref(v_query_1738_);
lean_dec_ref(v_m_1737_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object* v_00_u03b2_1740_, lean_object* v_m_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object* v_00_u03b2_1743_, lean_object* v_m_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_00_u03b2_1743_, v_m_1744_);
lean_dec_ref(v_m_1744_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object* v_00_u03b2_1746_, lean_object* v_m_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_m_1747_, v_a_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object* v_00_u03b2_1750_, lean_object* v_m_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_00_u03b2_1750_, v_m_1751_, v_a_1752_);
lean_dec_ref(v_a_1752_);
lean_dec_ref(v_m_1751_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object* v_00_u03b2_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_x_1755_, v_x_1756_, v_x_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object* v_00_u03b2_1759_, lean_object* v_m_1760_, lean_object* v_query_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_m_1760_, v_query_1761_, v_x_1762_, v_x_1763_, v_x_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1767_, lean_object* v_m_1768_, lean_object* v_query_1769_, lean_object* v_x_1770_, lean_object* v_x_1771_, lean_object* v_x_1772_, lean_object* v_x_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(v_00_u03b2_1767_, v_m_1768_, v_query_1769_, v_x_1770_, v_x_1771_, v_x_1772_, v_x_1773_);
lean_dec_ref(v_query_1769_);
lean_dec_ref(v_m_1768_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3(lean_object* v_00_u03b2_1775_, lean_object* v_init_1776_, lean_object* v_b_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3___redArg(v_init_1776_, v_b_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1779_, lean_object* v_init_1780_, lean_object* v_b_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3(v_00_u03b2_1779_, v_init_1780_, v_b_1781_);
lean_dec_ref(v_b_1781_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__5(lean_object* v_00_u03b2_1783_, lean_object* v_m_1784_, lean_object* v_query_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__5___redArg(v_m_1784_, v_query_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1787_, lean_object* v_m_1788_, lean_object* v_query_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__5(v_00_u03b2_1787_, v_m_1788_, v_query_1789_);
lean_dec_ref(v_query_1789_);
lean_dec_ref(v_m_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7_spec__12(lean_object* v_00_u03b1_1791_, lean_object* v_x_1792_, uint8_t v_isExporting_1793_, uint8_t v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7_spec__12___redArg(v_x_1792_, v_isExporting_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7_spec__12___boxed(lean_object* v_00_u03b1_1802_, lean_object* v_x_1803_, lean_object* v_isExporting_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
uint8_t v_isExporting_boxed_1812_; uint8_t v___y_35185__boxed_1813_; lean_object* v_res_1814_; 
v_isExporting_boxed_1812_ = lean_unbox(v_isExporting_1804_);
v___y_35185__boxed_1813_ = lean_unbox(v___y_1805_);
v_res_1814_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7_spec__12(v_00_u03b1_1802_, v_x_1803_, v_isExporting_boxed_1812_, v___y_35185__boxed_1813_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7(lean_object* v_00_u03b1_1815_, lean_object* v_x_1816_, uint8_t v_when_1817_, uint8_t v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_x_1816_, v_when_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1826_, lean_object* v_x_1827_, lean_object* v_when_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
uint8_t v_when_boxed_1836_; uint8_t v___y_35208__boxed_1837_; lean_object* v_res_1838_; 
v_when_boxed_1836_ = lean_unbox(v_when_1828_);
v___y_35208__boxed_1837_ = lean_unbox(v___y_1829_);
v_res_1838_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7(v_00_u03b1_1826_, v_x_1827_, v_when_boxed_1836_, v___y_35208__boxed_1837_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(lean_object* v_00_u03b2_1839_, lean_object* v_x_1840_, size_t v_x_1841_, size_t v_x_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_x_1840_, v_x_1841_, v_x_1842_, v_x_1843_, v_x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1846_, lean_object* v_x_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_){
_start:
{
size_t v_x_35232__boxed_1852_; size_t v_x_35233__boxed_1853_; lean_object* v_res_1854_; 
v_x_35232__boxed_1852_ = lean_unbox_usize(v_x_1848_);
lean_dec(v_x_1848_);
v_x_35233__boxed_1853_ = lean_unbox_usize(v_x_1849_);
lean_dec(v_x_1849_);
v_res_1854_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(v_00_u03b2_1846_, v_x_1847_, v_x_35232__boxed_1852_, v_x_35233__boxed_1853_, v_x_1850_, v_x_1851_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_1855_, lean_object* v_b_1856_, lean_object* v_acc_1857_, lean_object* v_i_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3_spec__7___redArg(v_b_1856_, v_acc_1857_, v_i_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1860_, lean_object* v_b_1861_, lean_object* v_acc_1862_, lean_object* v_i_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__3_spec__7(v_00_u03b2_1860_, v_b_1861_, v_acc_1862_, v_i_1863_);
lean_dec_ref(v_b_1861_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__15(lean_object* v_00_u03b2_1865_, lean_object* v_n_1866_, lean_object* v_k_1867_, lean_object* v_v_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__15___redArg(v_n_1866_, v_k_1867_, v_v_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1870_, size_t v_depth_1871_, lean_object* v_keys_1872_, lean_object* v_vals_1873_, lean_object* v_heq_1874_, lean_object* v_i_1875_, lean_object* v_entries_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__16___redArg(v_depth_1871_, v_keys_1872_, v_vals_1873_, v_i_1875_, v_entries_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1878_, lean_object* v_depth_1879_, lean_object* v_keys_1880_, lean_object* v_vals_1881_, lean_object* v_heq_1882_, lean_object* v_i_1883_, lean_object* v_entries_1884_){
_start:
{
size_t v_depth_boxed_1885_; lean_object* v_res_1886_; 
v_depth_boxed_1885_ = lean_unbox_usize(v_depth_1879_);
lean_dec(v_depth_1879_);
v_res_1886_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__16(v_00_u03b2_1878_, v_depth_boxed_1885_, v_keys_1880_, v_vals_1881_, v_heq_1882_, v_i_1883_, v_entries_1884_);
lean_dec_ref(v_vals_1881_);
lean_dec_ref(v_keys_1880_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__15_spec__18(lean_object* v_00_u03b2_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9_spec__15_spec__18___redArg(v_x_1888_, v_x_1889_, v_x_1890_, v_x_1891_);
return v___x_1892_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__0(void){
_start:
{
lean_object* v_cellCount_1893_; lean_object* v___x_1894_; 
v_cellCount_1893_ = lean_unsigned_to_nat(16u);
v___x_1894_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1893_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__1(void){
_start:
{
lean_object* v_cellCount_1895_; lean_object* v___x_1896_; 
v_cellCount_1895_ = lean_unsigned_to_nat(16u);
v___x_1896_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1895_);
return v___x_1896_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__2(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1897_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__1, &l_Lean_Meta_abstractNestedProofs___closed__1_once, _init_l_Lean_Meta_abstractNestedProofs___closed__1);
v___x_1898_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__0, &l_Lean_Meta_abstractNestedProofs___closed__0_once, _init_l_Lean_Meta_abstractNestedProofs___closed__0);
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v___x_1898_);
lean_ctor_set(v___x_1900_, 2, v___x_1897_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs(lean_object* v_e_1901_, uint8_t v_cache_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___x_1908_; 
lean_inc_ref(v_e_1901_);
v___x_1908_ = l_Lean_Meta_isProof(v_e_1901_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1929_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1929_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1929_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
uint8_t v___x_1913_; 
v___x_1913_ = lean_unbox(v_a_1909_);
lean_dec(v_a_1909_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_del_object(v___x_1911_);
v___x_1914_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__2, &l_Lean_Meta_abstractNestedProofs___closed__2_once, _init_l_Lean_Meta_abstractNestedProofs___closed__2);
v___x_1915_ = lean_st_mk_ref(v___x_1914_);
v___x_1916_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1901_, v_cache_1902_, v___x_1915_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1925_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = lean_st_ref_get(v___x_1915_);
lean_dec(v___x_1915_);
lean_dec(v___x_1921_);
if (v_isShared_1920_ == 0)
{
v___x_1923_ = v___x_1919_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1917_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
else
{
lean_dec(v___x_1915_);
return v___x_1916_;
}
}
else
{
lean_object* v___x_1927_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v_e_1901_);
v___x_1927_ = v___x_1911_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_e_1901_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v_e_1901_);
v_a_1930_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1908_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1908_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object* v_e_1938_, lean_object* v_cache_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
uint8_t v_cache_boxed_1945_; lean_object* v_res_1946_; 
v_cache_boxed_1945_ = lean_unbox(v_cache_1939_);
v_res_1946_ = l_Lean_Meta_abstractNestedProofs(v_e_1938_, v_cache_boxed_1945_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
return v_res_1946_;
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
