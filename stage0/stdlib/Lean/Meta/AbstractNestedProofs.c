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
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withoutExporting___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_toBind_75_);
lean_inc_ref(v_proof_72_);
v___x_76_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_76_, 0, v_proof_72_);
lean_inc(v_inst_69_);
v___x_77_ = lean_apply_2(v_inst_69_, lean_box(0), v___x_76_);
v___x_78_ = 1;
v___x_79_ = lean_box(v___x_78_);
v___x_80_ = lean_box(v_cache_73_);
lean_inc(v_inst_69_);
v___f_81_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_81_, 0, v_proof_72_);
lean_closure_set(v___f_81_, 1, v___x_79_);
lean_closure_set(v___f_81_, 2, v_inst_69_);
lean_closure_set(v___f_81_, 3, v___x_80_);
lean_inc(v_toBind_75_);
v___f_82_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__1), 4, 3);
lean_closure_set(v___f_82_, 0, v_postprocessType_74_);
lean_closure_set(v___f_82_, 1, v_toBind_75_);
lean_closure_set(v___f_82_, 2, v___f_81_);
v___x_83_ = lean_box(v___x_78_);
lean_inc(v_toBind_75_);
lean_inc(v_inst_69_);
v___f_84_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_84_, 0, v___x_83_);
lean_closure_set(v___f_84_, 1, v_inst_69_);
lean_closure_set(v___f_84_, 2, v_toBind_75_);
lean_closure_set(v___f_84_, 3, v___f_82_);
lean_inc(v_toBind_75_);
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
uint8_t v_a_4293__boxed_143_; uint8_t v___y_4294__boxed_144_; size_t v_i_boxed_145_; size_t v_stop_boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v_a_4293__boxed_143_ = lean_unbox(v_a_138_);
v___y_4294__boxed_144_ = lean_unbox(v___y_139_);
v_i_boxed_145_ = lean_unbox_usize(v_i_141_);
lean_dec(v_i_141_);
v_stop_boxed_146_ = lean_unbox_usize(v_stop_142_);
lean_dec(v_stop_142_);
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_4293__boxed_143_, v___y_4294__boxed_144_, v_as_140_, v_i_boxed_145_, v_stop_boxed_146_);
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
lean_dec_ref(v_x_152_);
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
lean_dec_ref(v_x_152_);
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
uint8_t v_a_4319__boxed_192_; uint8_t v___x_4320__boxed_193_; lean_object* v_res_194_; 
v_a_4319__boxed_192_ = lean_unbox(v_a_185_);
v___x_4320__boxed_193_ = lean_unbox(v___x_186_);
v_res_194_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_a_4319__boxed_192_, v___x_4320__boxed_193_, v___x_187_, v_x_188_, v_x_189_, v_x_190_);
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
v___x_264_ = lean_st_ref_set(v___y_242_, v___x_263_);
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
v___x_275_ = lean_st_ref_set(v___y_245_, v___x_274_);
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
lean_object* v___x_307_; lean_object* v_env_308_; uint8_t v_isExporting_309_; lean_object* v___x_310_; lean_object* v_env_311_; lean_object* v_nextMacroScope_312_; lean_object* v_ngen_313_; lean_object* v_auxDeclNGen_314_; lean_object* v_traceState_315_; lean_object* v_messages_316_; lean_object* v_infoState_317_; lean_object* v_snapshotTasks_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_372_; 
v___x_307_ = lean_st_ref_get(v___y_305_);
v_env_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc_ref(v_env_308_);
lean_dec(v___x_307_);
v_isExporting_309_ = lean_ctor_get_uint8(v_env_308_, sizeof(void*)*8);
lean_dec_ref(v_env_308_);
v___x_310_ = lean_st_ref_take(v___y_305_);
v_env_311_ = lean_ctor_get(v___x_310_, 0);
v_nextMacroScope_312_ = lean_ctor_get(v___x_310_, 1);
v_ngen_313_ = lean_ctor_get(v___x_310_, 2);
v_auxDeclNGen_314_ = lean_ctor_get(v___x_310_, 3);
v_traceState_315_ = lean_ctor_get(v___x_310_, 4);
v_messages_316_ = lean_ctor_get(v___x_310_, 6);
v_infoState_317_ = lean_ctor_get(v___x_310_, 7);
v_snapshotTasks_318_ = lean_ctor_get(v___x_310_, 8);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v___x_310_, 5);
lean_dec(v_unused_373_);
v___x_320_ = v___x_310_;
v_isShared_321_ = v_isSharedCheck_372_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_snapshotTasks_318_);
lean_inc(v_infoState_317_);
lean_inc(v_messages_316_);
lean_inc(v_traceState_315_);
lean_inc(v_auxDeclNGen_314_);
lean_inc(v_ngen_313_);
lean_inc(v_nextMacroScope_312_);
lean_inc(v_env_311_);
lean_dec(v___x_310_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_372_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_322_ = l_Lean_Environment_setExporting(v_env_311_, v_isExporting_301_);
v___x_323_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 5, v___x_323_);
lean_ctor_set(v___x_320_, 0, v___x_322_);
v___x_325_ = v___x_320_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_nextMacroScope_312_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_ngen_313_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v_auxDeclNGen_314_);
lean_ctor_set(v_reuseFailAlloc_371_, 4, v_traceState_315_);
lean_ctor_set(v_reuseFailAlloc_371_, 5, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_371_, 6, v_messages_316_);
lean_ctor_set(v_reuseFailAlloc_371_, 7, v_infoState_317_);
lean_ctor_set(v_reuseFailAlloc_371_, 8, v_snapshotTasks_318_);
v___x_325_ = v_reuseFailAlloc_371_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_mctx_328_; lean_object* v_zetaDeltaFVarIds_329_; lean_object* v_postponed_330_; lean_object* v_diag_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_369_; 
v___x_326_ = lean_st_ref_set(v___y_305_, v___x_325_);
v___x_327_ = lean_st_ref_take(v___y_303_);
v_mctx_328_ = lean_ctor_get(v___x_327_, 0);
v_zetaDeltaFVarIds_329_ = lean_ctor_get(v___x_327_, 2);
v_postponed_330_ = lean_ctor_get(v___x_327_, 3);
v_diag_331_ = lean_ctor_get(v___x_327_, 4);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v___x_327_, 1);
lean_dec(v_unused_370_);
v___x_333_ = v___x_327_;
v_isShared_334_ = v_isSharedCheck_369_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_diag_331_);
lean_inc(v_postponed_330_);
lean_inc(v_zetaDeltaFVarIds_329_);
lean_inc(v_mctx_328_);
lean_dec(v___x_327_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_369_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_335_);
v___x_337_ = v___x_333_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_mctx_328_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_zetaDeltaFVarIds_329_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v_postponed_330_);
lean_ctor_set(v_reuseFailAlloc_368_, 4, v_diag_331_);
v___x_337_ = v_reuseFailAlloc_368_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v_r_339_; 
v___x_338_ = lean_st_ref_set(v___y_303_, v___x_337_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v_r_339_ = lean_apply_5(v_x_300_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, lean_box(0));
if (lean_obj_tag(v_r_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_356_; 
v_a_340_ = lean_ctor_get(v_r_339_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v_r_339_);
if (v_isSharedCheck_356_ == 0)
{
v___x_342_ = v_r_339_;
v_isShared_343_ = v_isSharedCheck_356_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v_r_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_356_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
lean_inc(v_a_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set_tag(v___x_342_, 1);
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_355_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v___x_346_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_305_, v_isExporting_309_, v___x_323_, v___y_303_, v___x_335_, v___x_345_);
lean_dec_ref(v___x_345_);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; 
v_unused_354_ = lean_ctor_get(v___x_346_, 0);
lean_dec(v_unused_354_);
v___x_348_ = v___x_346_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_dec(v___x_346_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v_a_340_);
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_340_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_357_ = lean_ctor_get(v_r_339_, 0);
lean_inc(v_a_357_);
lean_dec_ref(v_r_339_);
v___x_358_ = lean_box(0);
v___x_359_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_305_, v_isExporting_309_, v___x_323_, v___y_303_, v___x_335_, v___x_358_);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; 
v_unused_367_ = lean_ctor_get(v___x_359_, 0);
lean_dec(v_unused_367_);
v___x_361_ = v___x_359_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_dec(v___x_359_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set_tag(v___x_361_, 1);
lean_ctor_set(v___x_361_, 0, v_a_357_);
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_357_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___boxed(lean_object* v_x_374_, lean_object* v_isExporting_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
uint8_t v_isExporting_boxed_381_; lean_object* v_res_382_; 
v_isExporting_boxed_381_ = lean_unbox(v_isExporting_375_);
v_res_382_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_374_, v_isExporting_boxed_381_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object* v_x_383_, uint8_t v_when_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
if (v_when_384_ == 0)
{
lean_object* v___x_390_; 
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
lean_inc(v___y_386_);
lean_inc_ref(v___y_385_);
v___x_390_ = lean_apply_5(v_x_383_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, lean_box(0));
return v___x_390_;
}
else
{
uint8_t v___x_391_; lean_object* v___x_392_; 
v___x_391_ = 0;
v___x_392_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_383_, v___x_391_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object* v_x_393_, lean_object* v_when_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
uint8_t v_when_boxed_400_; lean_object* v_res_401_; 
v_when_boxed_400_ = lean_unbox(v_when_394_);
v_res_401_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_393_, v_when_boxed_400_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object* v_e_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; lean_object* v_env_409_; lean_object* v___f_410_; uint8_t v___x_411_; lean_object* v___x_412_; 
v___x_408_ = lean_st_ref_get(v_a_406_);
v_env_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc_ref(v_env_409_);
lean_dec(v___x_408_);
v___f_410_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed), 7, 2);
lean_closure_set(v___f_410_, 0, v_e_402_);
lean_closure_set(v___f_410_, 1, v_env_409_);
v___x_411_ = 1;
v___x_412_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v___f_410_, v___x_411_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object* v_e_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(uint8_t v_a_420_, uint8_t v___x_421_, lean_object* v___x_422_, lean_object* v_x_423_, lean_object* v_x_424_, lean_object* v_x_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_a_420_, v___x_421_, v___x_422_, v_x_423_, v_x_424_, v_x_425_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object* v_a_432_, lean_object* v___x_433_, lean_object* v___x_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
uint8_t v_a_4730__boxed_443_; uint8_t v___x_4731__boxed_444_; lean_object* v_res_445_; 
v_a_4730__boxed_443_ = lean_unbox(v_a_432_);
v___x_4731__boxed_444_ = lean_unbox(v___x_433_);
v_res_445_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(v_a_4730__boxed_443_, v___x_4731__boxed_444_, v___x_434_, v_x_435_, v_x_436_, v_x_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(lean_object* v_00_u03b1_446_, lean_object* v_x_447_, uint8_t v_isExporting_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_447_, v_isExporting_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___boxed(lean_object* v_00_u03b1_455_, lean_object* v_x_456_, lean_object* v_isExporting_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
uint8_t v_isExporting_boxed_463_; lean_object* v_res_464_; 
v_isExporting_boxed_463_ = lean_unbox(v_isExporting_457_);
v_res_464_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(v_00_u03b1_455_, v_x_456_, v_isExporting_boxed_463_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object* v_00_u03b1_465_, lean_object* v_x_466_, uint8_t v_when_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_466_, v_when_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object* v_00_u03b1_474_, lean_object* v_x_475_, lean_object* v_when_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
uint8_t v_when_boxed_482_; lean_object* v_res_483_; 
v_when_boxed_482_ = lean_unbox(v_when_476_);
v_res_483_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(v_00_u03b1_474_, v_x_475_, v_when_boxed_482_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(lean_object* v_x_484_, uint8_t v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_box(v___y_485_);
lean_inc(v___y_486_);
v___x_493_ = lean_apply_7(v_x_484_, v___x_492_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, lean_box(0));
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed(lean_object* v_x_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
uint8_t v___y_26491__boxed_502_; lean_object* v_res_503_; 
v___y_26491__boxed_502_ = lean_unbox(v___y_495_);
v_res_503_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(v_x_494_, v___y_26491__boxed_502_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec(v___y_496_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(lean_object* v_lctx_504_, lean_object* v_localInsts_505_, lean_object* v_x_506_, uint8_t v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; lean_object* v___f_515_; lean_object* v___x_516_; 
v___x_514_ = lean_box(v___y_507_);
lean_inc(v___y_508_);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_515_, 0, v_x_506_);
lean_closure_set(v___f_515_, 1, v___x_514_);
lean_closure_set(v___f_515_, 2, v___y_508_);
v___x_516_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_504_, v_localInsts_505_, v___f_515_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
if (lean_obj_tag(v___x_516_) == 0)
{
return v___x_516_;
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___boxed(lean_object* v_lctx_525_, lean_object* v_localInsts_526_, lean_object* v_x_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
uint8_t v___y_26516__boxed_535_; lean_object* v_res_536_; 
v___y_26516__boxed_535_ = lean_unbox(v___y_528_);
v_res_536_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_lctx_525_, v_localInsts_526_, v_x_527_, v___y_26516__boxed_535_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object* v_00_u03b1_537_, lean_object* v_lctx_538_, lean_object* v_localInsts_539_, lean_object* v_x_540_, uint8_t v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_lctx_538_, v_localInsts_539_, v_x_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object* v_00_u03b1_549_, lean_object* v_lctx_550_, lean_object* v_localInsts_551_, lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
uint8_t v___y_26560__boxed_560_; lean_object* v_res_561_; 
v___y_26560__boxed_560_ = lean_unbox(v___y_553_);
v_res_561_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_00_u03b1_549_, v_lctx_550_, v_localInsts_551_, v_x_552_, v___y_26560__boxed_560_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(lean_object* v_k_562_, uint8_t v___y_563_, lean_object* v___y_564_, lean_object* v_b_565_, lean_object* v_c_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_box(v___y_563_);
lean_inc(v___y_570_);
lean_inc_ref(v___y_569_);
lean_inc(v___y_568_);
lean_inc_ref(v___y_567_);
lean_inc(v___y_564_);
v___x_573_ = lean_apply_9(v_k_562_, v_b_565_, v_c_566_, v___x_572_, v___y_564_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, lean_box(0));
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed(lean_object* v_k_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v_b_577_, lean_object* v_c_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
uint8_t v___y_26583__boxed_584_; lean_object* v_res_585_; 
v___y_26583__boxed_584_ = lean_unbox(v___y_575_);
v_res_585_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(v_k_574_, v___y_26583__boxed_584_, v___y_576_, v_b_577_, v_c_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_576_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object* v_e_586_, lean_object* v_k_587_, uint8_t v_cleanupAnnotations_588_, uint8_t v_preserveNondepLet_589_, uint8_t v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; lean_object* v___f_598_; uint8_t v___x_599_; uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_597_ = lean_box(v___y_590_);
lean_inc(v___y_591_);
v___f_598_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_598_, 0, v_k_587_);
lean_closure_set(v___f_598_, 1, v___x_597_);
lean_closure_set(v___f_598_, 2, v___y_591_);
v___x_599_ = 1;
v___x_600_ = 0;
v___x_601_ = lean_box(0);
v___x_602_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_586_, v___x_599_, v___x_599_, v_preserveNondepLet_589_, v___x_600_, v___x_601_, v___f_598_, v_cleanupAnnotations_588_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_602_) == 0)
{
return v___x_602_;
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object* v_e_611_, lean_object* v_k_612_, lean_object* v_cleanupAnnotations_613_, lean_object* v_preserveNondepLet_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_622_; uint8_t v_preserveNondepLet_boxed_623_; uint8_t v___y_26608__boxed_624_; lean_object* v_res_625_; 
v_cleanupAnnotations_boxed_622_ = lean_unbox(v_cleanupAnnotations_613_);
v_preserveNondepLet_boxed_623_ = lean_unbox(v_preserveNondepLet_614_);
v___y_26608__boxed_624_ = lean_unbox(v___y_615_);
v_res_625_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_611_, v_k_612_, v_cleanupAnnotations_boxed_622_, v_preserveNondepLet_boxed_623_, v___y_26608__boxed_624_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object* v_00_u03b1_626_, lean_object* v_e_627_, lean_object* v_k_628_, uint8_t v_cleanupAnnotations_629_, uint8_t v_preserveNondepLet_630_, uint8_t v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_627_, v_k_628_, v_cleanupAnnotations_629_, v_preserveNondepLet_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object* v_00_u03b1_639_, lean_object* v_e_640_, lean_object* v_k_641_, lean_object* v_cleanupAnnotations_642_, lean_object* v_preserveNondepLet_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_651_; uint8_t v_preserveNondepLet_boxed_652_; uint8_t v___y_26658__boxed_653_; lean_object* v_res_654_; 
v_cleanupAnnotations_boxed_651_ = lean_unbox(v_cleanupAnnotations_642_);
v_preserveNondepLet_boxed_652_ = lean_unbox(v_preserveNondepLet_643_);
v___y_26658__boxed_653_ = lean_unbox(v___y_644_);
v_res_654_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(v_00_u03b1_639_, v_e_640_, v_k_641_, v_cleanupAnnotations_boxed_651_, v_preserveNondepLet_boxed_652_, v___y_26658__boxed_653_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(lean_object* v_type_655_, lean_object* v_k_656_, uint8_t v_cleanupAnnotations_657_, uint8_t v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; lean_object* v___f_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_665_ = lean_box(v___y_658_);
lean_inc(v___y_659_);
v___f_666_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_666_, 0, v_k_656_);
lean_closure_set(v___f_666_, 1, v___x_665_);
lean_closure_set(v___f_666_, 2, v___y_659_);
v___x_667_ = 0;
v___x_668_ = lean_box(0);
v___x_669_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_667_, v___x_668_, v_type_655_, v___f_666_, v_cleanupAnnotations_657_, v___x_667_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_669_) == 0)
{
return v___x_669_;
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___boxed(lean_object* v_type_678_, lean_object* v_k_679_, lean_object* v_cleanupAnnotations_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_688_; uint8_t v___y_26681__boxed_689_; lean_object* v_res_690_; 
v_cleanupAnnotations_boxed_688_ = lean_unbox(v_cleanupAnnotations_680_);
v___y_26681__boxed_689_ = lean_unbox(v___y_681_);
v_res_690_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_678_, v_k_679_, v_cleanupAnnotations_boxed_688_, v___y_26681__boxed_689_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object* v_00_u03b1_691_, lean_object* v_type_692_, lean_object* v_k_693_, uint8_t v_cleanupAnnotations_694_, uint8_t v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_692_, v_k_693_, v_cleanupAnnotations_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object* v_00_u03b1_703_, lean_object* v_type_704_, lean_object* v_k_705_, lean_object* v_cleanupAnnotations_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_714_; uint8_t v___y_26729__boxed_715_; lean_object* v_res_716_; 
v_cleanupAnnotations_boxed_714_ = lean_unbox(v_cleanupAnnotations_706_);
v___y_26729__boxed_715_ = lean_unbox(v___y_707_);
v_res_716_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_00_u03b1_703_, v_type_704_, v_k_705_, v_cleanupAnnotations_boxed_714_, v___y_26729__boxed_715_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
lean_object* v_ks_721_; lean_object* v_vs_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_746_; 
v_ks_721_ = lean_ctor_get(v_x_717_, 0);
v_vs_722_ = lean_ctor_get(v_x_717_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_717_);
if (v_isSharedCheck_746_ == 0)
{
v___x_724_ = v_x_717_;
v_isShared_725_ = v_isSharedCheck_746_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_vs_722_);
lean_inc(v_ks_721_);
lean_dec(v_x_717_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_746_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = lean_array_get_size(v_ks_721_);
v___x_727_ = lean_nat_dec_lt(v_x_718_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
lean_dec(v_x_718_);
v___x_728_ = lean_array_push(v_ks_721_, v_x_719_);
v___x_729_ = lean_array_push(v_vs_722_, v_x_720_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v___x_729_);
lean_ctor_set(v___x_724_, 0, v___x_728_);
v___x_731_ = v___x_724_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
else
{
lean_object* v_k_x27_733_; uint8_t v___x_734_; 
v_k_x27_733_ = lean_array_fget_borrowed(v_ks_721_, v_x_718_);
v___x_734_ = l_Lean_instBEqFVarId_beq(v_x_719_, v_k_x27_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_736_; 
if (v_isShared_725_ == 0)
{
v___x_736_ = v___x_724_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_ks_721_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_vs_722_);
v___x_736_ = v_reuseFailAlloc_740_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_add(v_x_718_, v___x_737_);
lean_dec(v_x_718_);
v_x_717_ = v___x_736_;
v_x_718_ = v___x_738_;
goto _start;
}
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_741_ = lean_array_fset(v_ks_721_, v_x_718_, v_x_719_);
v___x_742_ = lean_array_fset(v_vs_722_, v_x_718_, v_x_720_);
lean_dec(v_x_718_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v___x_742_);
lean_ctor_set(v___x_724_, 0, v___x_741_);
v___x_744_ = v___x_724_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(lean_object* v_n_747_, lean_object* v_k_748_, lean_object* v_v_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(v_n_747_, v___x_750_, v_k_748_, v_v_749_);
return v___x_751_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0(void){
_start:
{
size_t v___x_752_; size_t v___x_753_; size_t v___x_754_; 
v___x_752_ = ((size_t)5ULL);
v___x_753_ = ((size_t)1ULL);
v___x_754_ = lean_usize_shift_left(v___x_753_, v___x_752_);
return v___x_754_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1(void){
_start:
{
size_t v___x_755_; size_t v___x_756_; size_t v___x_757_; 
v___x_755_ = ((size_t)1ULL);
v___x_756_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0);
v___x_757_ = lean_usize_sub(v___x_756_, v___x_755_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(lean_object* v_x_759_, size_t v_x_760_, size_t v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
if (lean_obj_tag(v_x_759_) == 0)
{
lean_object* v_es_764_; size_t v___x_765_; size_t v___x_766_; size_t v___x_767_; size_t v___x_768_; lean_object* v_j_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_es_764_ = lean_ctor_get(v_x_759_, 0);
v___x_765_ = ((size_t)5ULL);
v___x_766_ = ((size_t)1ULL);
v___x_767_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1);
v___x_768_ = lean_usize_land(v_x_760_, v___x_767_);
v_j_769_ = lean_usize_to_nat(v___x_768_);
v___x_770_ = lean_array_get_size(v_es_764_);
v___x_771_ = lean_nat_dec_lt(v_j_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_dec(v_j_769_);
lean_dec(v_x_763_);
lean_dec(v_x_762_);
return v_x_759_;
}
else
{
lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_808_; 
lean_inc_ref(v_es_764_);
v_isSharedCheck_808_ = !lean_is_exclusive(v_x_759_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v_x_759_, 0);
lean_dec(v_unused_809_);
v___x_773_ = v_x_759_;
v_isShared_774_ = v_isSharedCheck_808_;
goto v_resetjp_772_;
}
else
{
lean_dec(v_x_759_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_808_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_v_775_; lean_object* v___x_776_; lean_object* v_xs_x27_777_; lean_object* v___y_779_; 
v_v_775_ = lean_array_fget(v_es_764_, v_j_769_);
v___x_776_ = lean_box(0);
v_xs_x27_777_ = lean_array_fset(v_es_764_, v_j_769_, v___x_776_);
switch(lean_obj_tag(v_v_775_))
{
case 0:
{
lean_object* v_key_784_; lean_object* v_val_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_795_; 
v_key_784_ = lean_ctor_get(v_v_775_, 0);
v_val_785_ = lean_ctor_get(v_v_775_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_v_775_);
if (v_isSharedCheck_795_ == 0)
{
v___x_787_ = v_v_775_;
v_isShared_788_ = v_isSharedCheck_795_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_val_785_);
lean_inc(v_key_784_);
lean_dec(v_v_775_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_795_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
uint8_t v___x_789_; 
v___x_789_ = l_Lean_instBEqFVarId_beq(v_x_762_, v_key_784_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; 
lean_del_object(v___x_787_);
v___x_790_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_784_, v_val_785_, v_x_762_, v_x_763_);
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
v___y_779_ = v___x_791_;
goto v___jp_778_;
}
else
{
lean_object* v___x_793_; 
lean_dec(v_val_785_);
lean_dec(v_key_784_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v_x_763_);
lean_ctor_set(v___x_787_, 0, v_x_762_);
v___x_793_ = v___x_787_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_x_762_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_x_763_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
v___y_779_ = v___x_793_;
goto v___jp_778_;
}
}
}
}
case 1:
{
lean_object* v_node_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_806_; 
v_node_796_ = lean_ctor_get(v_v_775_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_v_775_);
if (v_isSharedCheck_806_ == 0)
{
v___x_798_ = v_v_775_;
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_node_796_);
lean_dec(v_v_775_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_800_ = lean_usize_shift_right(v_x_760_, v___x_765_);
v___x_801_ = lean_usize_add(v_x_761_, v___x_766_);
v___x_802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_node_796_, v___x_800_, v___x_801_, v_x_762_, v_x_763_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_802_);
v___x_804_ = v___x_798_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
v___y_779_ = v___x_804_;
goto v___jp_778_;
}
}
}
default: 
{
lean_object* v___x_807_; 
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_x_762_);
lean_ctor_set(v___x_807_, 1, v_x_763_);
v___y_779_ = v___x_807_;
goto v___jp_778_;
}
}
v___jp_778_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_array_fset(v_xs_x27_777_, v_j_769_, v___y_779_);
lean_dec(v_j_769_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_780_);
v___x_782_ = v___x_773_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
else
{
lean_object* v_ks_810_; lean_object* v_vs_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_831_; 
v_ks_810_ = lean_ctor_get(v_x_759_, 0);
v_vs_811_ = lean_ctor_get(v_x_759_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_x_759_);
if (v_isSharedCheck_831_ == 0)
{
v___x_813_ = v_x_759_;
v_isShared_814_ = v_isSharedCheck_831_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_vs_811_);
lean_inc(v_ks_810_);
lean_dec(v_x_759_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_831_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_ks_810_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_vs_811_);
v___x_816_ = v_reuseFailAlloc_830_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v_newNode_817_; uint8_t v___y_819_; size_t v___x_825_; uint8_t v___x_826_; 
v_newNode_817_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(v___x_816_, v_x_762_, v_x_763_);
v___x_825_ = ((size_t)7ULL);
v___x_826_ = lean_usize_dec_le(v___x_825_, v_x_761_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_827_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_817_);
v___x_828_ = lean_unsigned_to_nat(4u);
v___x_829_ = lean_nat_dec_lt(v___x_827_, v___x_828_);
lean_dec(v___x_827_);
v___y_819_ = v___x_829_;
goto v___jp_818_;
}
else
{
v___y_819_ = v___x_826_;
goto v___jp_818_;
}
v___jp_818_:
{
if (v___y_819_ == 0)
{
lean_object* v_ks_820_; lean_object* v_vs_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_ks_820_ = lean_ctor_get(v_newNode_817_, 0);
lean_inc_ref(v_ks_820_);
v_vs_821_ = lean_ctor_get(v_newNode_817_, 1);
lean_inc_ref(v_vs_821_);
lean_dec_ref(v_newNode_817_);
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2);
v___x_824_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_x_761_, v_ks_820_, v_vs_821_, v___x_822_, v___x_823_);
lean_dec_ref(v_vs_821_);
lean_dec_ref(v_ks_820_);
return v___x_824_;
}
else
{
return v_newNode_817_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(size_t v_depth_832_, lean_object* v_keys_833_, lean_object* v_vals_834_, lean_object* v_i_835_, lean_object* v_entries_836_){
_start:
{
lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_837_ = lean_array_get_size(v_keys_833_);
v___x_838_ = lean_nat_dec_lt(v_i_835_, v___x_837_);
if (v___x_838_ == 0)
{
lean_dec(v_i_835_);
return v_entries_836_;
}
else
{
lean_object* v_k_839_; lean_object* v_v_840_; uint64_t v___x_841_; size_t v_h_842_; size_t v___x_843_; lean_object* v___x_844_; size_t v___x_845_; size_t v___x_846_; size_t v___x_847_; size_t v_h_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_k_839_ = lean_array_fget_borrowed(v_keys_833_, v_i_835_);
v_v_840_ = lean_array_fget_borrowed(v_vals_834_, v_i_835_);
v___x_841_ = l_Lean_instHashableFVarId_hash(v_k_839_);
v_h_842_ = lean_uint64_to_usize(v___x_841_);
v___x_843_ = ((size_t)5ULL);
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = ((size_t)1ULL);
v___x_846_ = lean_usize_sub(v_depth_832_, v___x_845_);
v___x_847_ = lean_usize_mul(v___x_843_, v___x_846_);
v_h_848_ = lean_usize_shift_right(v_h_842_, v___x_847_);
v___x_849_ = lean_nat_add(v_i_835_, v___x_844_);
lean_dec(v_i_835_);
lean_inc(v_v_840_);
lean_inc(v_k_839_);
v___x_850_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_entries_836_, v_h_848_, v_depth_832_, v_k_839_, v_v_840_);
v_i_835_ = v___x_849_;
v_entries_836_ = v___x_850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg___boxed(lean_object* v_depth_852_, lean_object* v_keys_853_, lean_object* v_vals_854_, lean_object* v_i_855_, lean_object* v_entries_856_){
_start:
{
size_t v_depth_boxed_857_; lean_object* v_res_858_; 
v_depth_boxed_857_ = lean_unbox_usize(v_depth_852_);
lean_dec(v_depth_852_);
v_res_858_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_depth_boxed_857_, v_keys_853_, v_vals_854_, v_i_855_, v_entries_856_);
lean_dec_ref(v_vals_854_);
lean_dec_ref(v_keys_853_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___boxed(lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
size_t v_x_26841__boxed_864_; size_t v_x_26842__boxed_865_; lean_object* v_res_866_; 
v_x_26841__boxed_864_ = lean_unbox_usize(v_x_860_);
lean_dec(v_x_860_);
v_x_26842__boxed_865_ = lean_unbox_usize(v_x_861_);
lean_dec(v_x_861_);
v_res_866_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_859_, v_x_26841__boxed_864_, v_x_26842__boxed_865_, v_x_862_, v_x_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
uint64_t v___x_870_; size_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; 
v___x_870_ = l_Lean_instHashableFVarId_hash(v_x_868_);
v___x_871_ = lean_uint64_to_usize(v___x_870_);
v___x_872_ = ((size_t)1ULL);
v___x_873_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_867_, v___x_871_, v___x_872_, v_x_868_, v_x_869_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(lean_object* v_a_874_, lean_object* v_x_875_){
_start:
{
if (lean_obj_tag(v_x_875_) == 0)
{
lean_object* v___x_876_; 
v___x_876_ = lean_box(0);
return v___x_876_;
}
else
{
lean_object* v_key_877_; lean_object* v_value_878_; lean_object* v_tail_879_; uint8_t v___x_880_; 
v_key_877_ = lean_ctor_get(v_x_875_, 0);
v_value_878_ = lean_ctor_get(v_x_875_, 1);
v_tail_879_ = lean_ctor_get(v_x_875_, 2);
v___x_880_ = l_Lean_ExprStructEq_beq(v_key_877_, v_a_874_);
if (v___x_880_ == 0)
{
v_x_875_ = v_tail_879_;
goto _start;
}
else
{
lean_object* v___x_882_; 
lean_inc(v_value_878_);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v_value_878_);
return v___x_882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg___boxed(lean_object* v_a_883_, lean_object* v_x_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_883_, v_x_884_);
lean_dec(v_x_884_);
lean_dec_ref(v_a_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(lean_object* v_m_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_buckets_888_; lean_object* v___x_889_; uint64_t v___x_890_; uint64_t v___x_891_; uint64_t v___x_892_; uint64_t v_fold_893_; uint64_t v___x_894_; uint64_t v___x_895_; uint64_t v___x_896_; size_t v___x_897_; size_t v___x_898_; size_t v___x_899_; size_t v___x_900_; size_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_buckets_888_ = lean_ctor_get(v_m_886_, 1);
v___x_889_ = lean_array_get_size(v_buckets_888_);
v___x_890_ = l_Lean_ExprStructEq_hash(v_a_887_);
v___x_891_ = 32ULL;
v___x_892_ = lean_uint64_shift_right(v___x_890_, v___x_891_);
v_fold_893_ = lean_uint64_xor(v___x_890_, v___x_892_);
v___x_894_ = 16ULL;
v___x_895_ = lean_uint64_shift_right(v_fold_893_, v___x_894_);
v___x_896_ = lean_uint64_xor(v_fold_893_, v___x_895_);
v___x_897_ = lean_uint64_to_usize(v___x_896_);
v___x_898_ = lean_usize_of_nat(v___x_889_);
v___x_899_ = ((size_t)1ULL);
v___x_900_ = lean_usize_sub(v___x_898_, v___x_899_);
v___x_901_ = lean_usize_land(v___x_897_, v___x_900_);
v___x_902_ = lean_array_uget_borrowed(v_buckets_888_, v___x_901_);
v___x_903_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_887_, v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg___boxed(lean_object* v_m_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_904_, v_a_905_);
lean_dec_ref(v_a_905_);
lean_dec_ref(v_m_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(lean_object* v_x_907_, uint8_t v_isExporting_908_, uint8_t v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; lean_object* v_env_917_; uint8_t v_isExporting_918_; lean_object* v___x_919_; lean_object* v_env_920_; lean_object* v_nextMacroScope_921_; lean_object* v_ngen_922_; lean_object* v_auxDeclNGen_923_; lean_object* v_traceState_924_; lean_object* v_messages_925_; lean_object* v_infoState_926_; lean_object* v_snapshotTasks_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_982_; 
v___x_916_ = lean_st_ref_get(v___y_914_);
v_env_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc_ref(v_env_917_);
lean_dec(v___x_916_);
v_isExporting_918_ = lean_ctor_get_uint8(v_env_917_, sizeof(void*)*8);
lean_dec_ref(v_env_917_);
v___x_919_ = lean_st_ref_take(v___y_914_);
v_env_920_ = lean_ctor_get(v___x_919_, 0);
v_nextMacroScope_921_ = lean_ctor_get(v___x_919_, 1);
v_ngen_922_ = lean_ctor_get(v___x_919_, 2);
v_auxDeclNGen_923_ = lean_ctor_get(v___x_919_, 3);
v_traceState_924_ = lean_ctor_get(v___x_919_, 4);
v_messages_925_ = lean_ctor_get(v___x_919_, 6);
v_infoState_926_ = lean_ctor_get(v___x_919_, 7);
v_snapshotTasks_927_ = lean_ctor_get(v___x_919_, 8);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v___x_919_, 5);
lean_dec(v_unused_983_);
v___x_929_ = v___x_919_;
v_isShared_930_ = v_isSharedCheck_982_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_snapshotTasks_927_);
lean_inc(v_infoState_926_);
lean_inc(v_messages_925_);
lean_inc(v_traceState_924_);
lean_inc(v_auxDeclNGen_923_);
lean_inc(v_ngen_922_);
lean_inc(v_nextMacroScope_921_);
lean_inc(v_env_920_);
lean_dec(v___x_919_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_982_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_931_ = l_Lean_Environment_setExporting(v_env_920_, v_isExporting_908_);
v___x_932_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 5, v___x_932_);
lean_ctor_set(v___x_929_, 0, v___x_931_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_nextMacroScope_921_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_ngen_922_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_auxDeclNGen_923_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_traceState_924_);
lean_ctor_set(v_reuseFailAlloc_981_, 5, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_981_, 6, v_messages_925_);
lean_ctor_set(v_reuseFailAlloc_981_, 7, v_infoState_926_);
lean_ctor_set(v_reuseFailAlloc_981_, 8, v_snapshotTasks_927_);
v___x_934_ = v_reuseFailAlloc_981_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v_mctx_937_; lean_object* v_zetaDeltaFVarIds_938_; lean_object* v_postponed_939_; lean_object* v_diag_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_979_; 
v___x_935_ = lean_st_ref_set(v___y_914_, v___x_934_);
v___x_936_ = lean_st_ref_take(v___y_912_);
v_mctx_937_ = lean_ctor_get(v___x_936_, 0);
v_zetaDeltaFVarIds_938_ = lean_ctor_get(v___x_936_, 2);
v_postponed_939_ = lean_ctor_get(v___x_936_, 3);
v_diag_940_ = lean_ctor_get(v___x_936_, 4);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; 
v_unused_980_ = lean_ctor_get(v___x_936_, 1);
lean_dec(v_unused_980_);
v___x_942_ = v___x_936_;
v_isShared_943_ = v_isSharedCheck_979_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_diag_940_);
lean_inc(v_postponed_939_);
lean_inc(v_zetaDeltaFVarIds_938_);
lean_inc(v_mctx_937_);
lean_dec(v___x_936_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_979_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_mctx_937_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_zetaDeltaFVarIds_938_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_postponed_939_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_diag_940_);
v___x_946_ = v_reuseFailAlloc_978_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v_r_949_; 
v___x_947_ = lean_st_ref_set(v___y_912_, v___x_946_);
v___x_948_ = lean_box(v___y_909_);
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
v_r_949_ = lean_apply_7(v_x_907_, v___x_948_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, lean_box(0));
if (lean_obj_tag(v_r_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_966_; 
v_a_950_ = lean_ctor_get(v_r_949_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v_r_949_);
if (v_isSharedCheck_966_ == 0)
{
v___x_952_ = v_r_949_;
v_isShared_953_ = v_isSharedCheck_966_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v_r_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_966_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
lean_inc(v_a_950_);
if (v_isShared_953_ == 0)
{
lean_ctor_set_tag(v___x_952_, 1);
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_965_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v___x_956_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_914_, v_isExporting_918_, v___x_932_, v___y_912_, v___x_944_, v___x_955_);
lean_dec_ref(v___x_955_);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v___x_956_, 0);
lean_dec(v_unused_964_);
v___x_958_ = v___x_956_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_dec(v___x_956_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v_a_950_);
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_950_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_a_967_ = lean_ctor_get(v_r_949_, 0);
lean_inc(v_a_967_);
lean_dec_ref(v_r_949_);
v___x_968_ = lean_box(0);
v___x_969_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_914_, v_isExporting_918_, v___x_932_, v___y_912_, v___x_944_, v___x_968_);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v___x_969_, 0);
lean_dec(v_unused_977_);
v___x_971_ = v___x_969_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_dec(v___x_969_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 1);
lean_ctor_set(v___x_971_, 0, v_a_967_);
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_967_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg___boxed(lean_object* v_x_984_, lean_object* v_isExporting_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
uint8_t v_isExporting_boxed_993_; uint8_t v___y_27077__boxed_994_; lean_object* v_res_995_; 
v_isExporting_boxed_993_ = lean_unbox(v_isExporting_985_);
v___y_27077__boxed_994_ = lean_unbox(v___y_986_);
v_res_995_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_984_, v_isExporting_boxed_993_, v___y_27077__boxed_994_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(lean_object* v_x_996_, uint8_t v_when_997_, uint8_t v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
if (v_when_997_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_box(v___y_998_);
lean_inc(v___y_1003_);
lean_inc_ref(v___y_1002_);
lean_inc(v___y_1001_);
lean_inc_ref(v___y_1000_);
lean_inc(v___y_999_);
v___x_1006_ = lean_apply_7(v_x_996_, v___x_1005_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, lean_box(0));
return v___x_1006_;
}
else
{
uint8_t v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = 0;
v___x_1008_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_996_, v___x_1007_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___boxed(lean_object* v_x_1009_, lean_object* v_when_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
uint8_t v_when_boxed_1018_; uint8_t v___y_27210__boxed_1019_; lean_object* v_res_1020_; 
v_when_boxed_1018_ = lean_unbox(v_when_1010_);
v___y_27210__boxed_1019_ = lean_unbox(v___y_1011_);
v_res_1020_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_1009_, v_when_boxed_1018_, v___y_27210__boxed_1019_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0(lean_object* v_proof_1021_, uint8_t v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
lean_inc(v___y_1025_);
lean_inc_ref(v___y_1024_);
v___x_1029_ = lean_infer_type(v_proof_1021_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0___boxed(lean_object* v_proof_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
uint8_t v___y_27239__boxed_1038_; lean_object* v_res_1039_; 
v___y_27239__boxed_1038_ = lean_unbox(v___y_1031_);
v_res_1039_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0(v_proof_1030_, v___y_27239__boxed_1038_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object* v_proof_1040_, uint8_t v_cache_1041_, lean_object* v_postprocessType_1042_, uint8_t v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___f_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; 
lean_inc_ref(v_proof_1040_);
v___f_1050_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1050_, 0, v_proof_1040_);
v___x_1051_ = 1;
v___x_1052_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v___f_1050_, v___x_1051_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = l_Lean_Core_betaReduce(v_a_1053_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1056_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref(v___x_1054_);
lean_inc_ref(v___y_1045_);
v___x_1056_ = l_Lean_Meta_zetaReduce(v_a_1055_, v___x_1051_, v___x_1051_, v___x_1051_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = lean_box(v___y_1043_);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
lean_inc(v___y_1044_);
v___x_1059_ = lean_apply_8(v_postprocessType_1042_, v_a_1057_, v___x_1058_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, lean_box(0));
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; uint8_t v___y_1062_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref(v___x_1059_);
if (v_cache_1041_ == 0)
{
v___y_1062_ = v_cache_1041_;
goto v___jp_1061_;
}
else
{
uint8_t v___x_1065_; 
v___x_1065_ = l_Lean_Expr_hasSorry(v_proof_1040_);
if (v___x_1065_ == 0)
{
v___y_1062_ = v_cache_1041_;
goto v___jp_1061_;
}
else
{
uint8_t v___x_1066_; 
v___x_1066_ = 0;
v___y_1062_ = v___x_1066_;
goto v___jp_1061_;
}
}
v___jp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = l_Lean_Meta_mkAuxTheorem(v_a_1060_, v_proof_1040_, v___x_1051_, v___x_1063_, v___y_1062_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1064_;
}
}
else
{
lean_dec_ref(v_proof_1040_);
return v___x_1059_;
}
}
else
{
lean_dec_ref(v_postprocessType_1042_);
lean_dec_ref(v_proof_1040_);
return v___x_1056_;
}
}
else
{
lean_dec_ref(v_postprocessType_1042_);
lean_dec_ref(v_proof_1040_);
return v___x_1054_;
}
}
else
{
lean_dec_ref(v_postprocessType_1042_);
lean_dec_ref(v_proof_1040_);
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object* v_proof_1067_, lean_object* v_cache_1068_, lean_object* v_postprocessType_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
uint8_t v_cache_boxed_1077_; uint8_t v___y_27262__boxed_1078_; lean_object* v_res_1079_; 
v_cache_boxed_1077_ = lean_unbox(v_cache_1068_);
v___y_27262__boxed_1078_ = lean_unbox(v___y_1070_);
v_res_1079_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_proof_1067_, v_cache_boxed_1077_, v_postprocessType_1069_, v___y_27262__boxed_1078_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
if (lean_obj_tag(v_x_1081_) == 0)
{
return v_x_1080_;
}
else
{
lean_object* v_key_1082_; lean_object* v_value_1083_; lean_object* v_tail_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1107_; 
v_key_1082_ = lean_ctor_get(v_x_1081_, 0);
v_value_1083_ = lean_ctor_get(v_x_1081_, 1);
v_tail_1084_ = lean_ctor_get(v_x_1081_, 2);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_x_1081_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1086_ = v_x_1081_;
v_isShared_1087_ = v_isSharedCheck_1107_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_tail_1084_);
lean_inc(v_value_1083_);
lean_inc(v_key_1082_);
lean_dec(v_x_1081_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1107_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; uint64_t v___x_1089_; uint64_t v___x_1090_; uint64_t v___x_1091_; uint64_t v_fold_1092_; uint64_t v___x_1093_; uint64_t v___x_1094_; uint64_t v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; size_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1088_ = lean_array_get_size(v_x_1080_);
v___x_1089_ = l_Lean_ExprStructEq_hash(v_key_1082_);
v___x_1090_ = 32ULL;
v___x_1091_ = lean_uint64_shift_right(v___x_1089_, v___x_1090_);
v_fold_1092_ = lean_uint64_xor(v___x_1089_, v___x_1091_);
v___x_1093_ = 16ULL;
v___x_1094_ = lean_uint64_shift_right(v_fold_1092_, v___x_1093_);
v___x_1095_ = lean_uint64_xor(v_fold_1092_, v___x_1094_);
v___x_1096_ = lean_uint64_to_usize(v___x_1095_);
v___x_1097_ = lean_usize_of_nat(v___x_1088_);
v___x_1098_ = ((size_t)1ULL);
v___x_1099_ = lean_usize_sub(v___x_1097_, v___x_1098_);
v___x_1100_ = lean_usize_land(v___x_1096_, v___x_1099_);
v___x_1101_ = lean_array_uget_borrowed(v_x_1080_, v___x_1100_);
lean_inc(v___x_1101_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 2, v___x_1101_);
v___x_1103_ = v___x_1086_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_key_1082_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_value_1083_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_array_uset(v_x_1080_, v___x_1100_, v___x_1103_);
v_x_1080_ = v___x_1104_;
v_x_1081_ = v_tail_1084_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(lean_object* v_i_1108_, lean_object* v_source_1109_, lean_object* v_target_1110_){
_start:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_array_get_size(v_source_1109_);
v___x_1112_ = lean_nat_dec_lt(v_i_1108_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_dec_ref(v_source_1109_);
lean_dec(v_i_1108_);
return v_target_1110_;
}
else
{
lean_object* v_es_1113_; lean_object* v___x_1114_; lean_object* v_source_1115_; lean_object* v_target_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_es_1113_ = lean_array_fget(v_source_1109_, v_i_1108_);
v___x_1114_ = lean_box(0);
v_source_1115_ = lean_array_fset(v_source_1109_, v_i_1108_, v___x_1114_);
v_target_1116_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(v_target_1110_, v_es_1113_);
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_add(v_i_1108_, v___x_1117_);
lean_dec(v_i_1108_);
v_i_1108_ = v___x_1118_;
v_source_1109_ = v_source_1115_;
v_target_1110_ = v_target_1116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(lean_object* v_data_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_nbuckets_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1121_ = lean_array_get_size(v_data_1120_);
v___x_1122_ = lean_unsigned_to_nat(2u);
v_nbuckets_1123_ = lean_nat_mul(v___x_1121_, v___x_1122_);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_mk_array(v_nbuckets_1123_, v___x_1125_);
v___x_1127_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(v___x_1124_, v_data_1120_, v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object* v_a_1128_, lean_object* v_x_1129_){
_start:
{
if (lean_obj_tag(v_x_1129_) == 0)
{
uint8_t v___x_1130_; 
v___x_1130_ = 0;
return v___x_1130_;
}
else
{
lean_object* v_key_1131_; lean_object* v_tail_1132_; uint8_t v___x_1133_; 
v_key_1131_ = lean_ctor_get(v_x_1129_, 0);
v_tail_1132_ = lean_ctor_get(v_x_1129_, 2);
v___x_1133_ = l_Lean_ExprStructEq_beq(v_key_1131_, v_a_1128_);
if (v___x_1133_ == 0)
{
v_x_1129_ = v_tail_1132_;
goto _start;
}
else
{
return v___x_1133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_1135_, lean_object* v_x_1136_){
_start:
{
uint8_t v_res_1137_; lean_object* v_r_1138_; 
v_res_1137_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1135_, v_x_1136_);
lean_dec(v_x_1136_);
lean_dec_ref(v_a_1135_);
v_r_1138_ = lean_box(v_res_1137_);
return v_r_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(lean_object* v_a_1139_, lean_object* v_b_1140_, lean_object* v_x_1141_){
_start:
{
if (lean_obj_tag(v_x_1141_) == 0)
{
lean_dec(v_b_1140_);
lean_dec_ref(v_a_1139_);
return v_x_1141_;
}
else
{
lean_object* v_key_1142_; lean_object* v_value_1143_; lean_object* v_tail_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1156_; 
v_key_1142_ = lean_ctor_get(v_x_1141_, 0);
v_value_1143_ = lean_ctor_get(v_x_1141_, 1);
v_tail_1144_ = lean_ctor_get(v_x_1141_, 2);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_x_1141_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1146_ = v_x_1141_;
v_isShared_1147_ = v_isSharedCheck_1156_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_tail_1144_);
lean_inc(v_value_1143_);
lean_inc(v_key_1142_);
lean_dec(v_x_1141_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1156_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
uint8_t v___x_1148_; 
v___x_1148_ = l_Lean_ExprStructEq_beq(v_key_1142_, v_a_1139_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1139_, v_b_1140_, v_tail_1144_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 2, v___x_1149_);
v___x_1151_ = v___x_1146_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_key_1142_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_value_1143_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
else
{
lean_object* v___x_1154_; 
lean_dec(v_value_1143_);
lean_dec(v_key_1142_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 1, v_b_1140_);
lean_ctor_set(v___x_1146_, 0, v_a_1139_);
v___x_1154_ = v___x_1146_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1139_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_b_1140_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_tail_1144_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object* v_m_1157_, lean_object* v_a_1158_, lean_object* v_b_1159_){
_start:
{
lean_object* v_size_1160_; lean_object* v_buckets_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1204_; 
v_size_1160_ = lean_ctor_get(v_m_1157_, 0);
v_buckets_1161_ = lean_ctor_get(v_m_1157_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_m_1157_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1163_ = v_m_1157_;
v_isShared_1164_ = v_isSharedCheck_1204_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_buckets_1161_);
lean_inc(v_size_1160_);
lean_dec(v_m_1157_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1204_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; uint64_t v___x_1166_; uint64_t v___x_1167_; uint64_t v___x_1168_; uint64_t v_fold_1169_; uint64_t v___x_1170_; uint64_t v___x_1171_; uint64_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; lean_object* v_bkt_1178_; uint8_t v___x_1179_; 
v___x_1165_ = lean_array_get_size(v_buckets_1161_);
v___x_1166_ = l_Lean_ExprStructEq_hash(v_a_1158_);
v___x_1167_ = 32ULL;
v___x_1168_ = lean_uint64_shift_right(v___x_1166_, v___x_1167_);
v_fold_1169_ = lean_uint64_xor(v___x_1166_, v___x_1168_);
v___x_1170_ = 16ULL;
v___x_1171_ = lean_uint64_shift_right(v_fold_1169_, v___x_1170_);
v___x_1172_ = lean_uint64_xor(v_fold_1169_, v___x_1171_);
v___x_1173_ = lean_uint64_to_usize(v___x_1172_);
v___x_1174_ = lean_usize_of_nat(v___x_1165_);
v___x_1175_ = ((size_t)1ULL);
v___x_1176_ = lean_usize_sub(v___x_1174_, v___x_1175_);
v___x_1177_ = lean_usize_land(v___x_1173_, v___x_1176_);
v_bkt_1178_ = lean_array_uget_borrowed(v_buckets_1161_, v___x_1177_);
v___x_1179_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1158_, v_bkt_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v_size_x27_1181_; lean_object* v___x_1182_; lean_object* v_buckets_x27_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1180_ = lean_unsigned_to_nat(1u);
v_size_x27_1181_ = lean_nat_add(v_size_1160_, v___x_1180_);
lean_dec(v_size_1160_);
lean_inc(v_bkt_1178_);
v___x_1182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1182_, 0, v_a_1158_);
lean_ctor_set(v___x_1182_, 1, v_b_1159_);
lean_ctor_set(v___x_1182_, 2, v_bkt_1178_);
v_buckets_x27_1183_ = lean_array_uset(v_buckets_1161_, v___x_1177_, v___x_1182_);
v___x_1184_ = lean_unsigned_to_nat(4u);
v___x_1185_ = lean_nat_mul(v_size_x27_1181_, v___x_1184_);
v___x_1186_ = lean_unsigned_to_nat(3u);
v___x_1187_ = lean_nat_div(v___x_1185_, v___x_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_array_get_size(v_buckets_x27_1183_);
v___x_1189_ = lean_nat_dec_le(v___x_1187_, v___x_1188_);
lean_dec(v___x_1187_);
if (v___x_1189_ == 0)
{
lean_object* v_val_1190_; lean_object* v___x_1192_; 
v_val_1190_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(v_buckets_x27_1183_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v_val_1190_);
lean_ctor_set(v___x_1163_, 0, v_size_x27_1181_);
v___x_1192_ = v___x_1163_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_size_x27_1181_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_val_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
else
{
lean_object* v___x_1195_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v_buckets_x27_1183_);
lean_ctor_set(v___x_1163_, 0, v_size_x27_1181_);
v___x_1195_ = v___x_1163_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_size_x27_1181_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_buckets_x27_1183_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
else
{
lean_object* v___x_1197_; lean_object* v_buckets_x27_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
lean_inc(v_bkt_1178_);
v___x_1197_ = lean_box(0);
v_buckets_x27_1198_ = lean_array_uset(v_buckets_1161_, v___x_1177_, v___x_1197_);
v___x_1199_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1158_, v_b_1159_, v_bkt_1178_);
v___x_1200_ = lean_array_uset(v_buckets_x27_1198_, v___x_1177_, v___x_1199_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1200_);
v___x_1202_ = v___x_1163_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_size_1160_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object* v_e_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
uint8_t v_a_boxed_1213_; lean_object* v_res_1214_; 
v_a_boxed_1213_ = lean_unbox(v_a_1206_);
v_res_1214_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1205_, v_a_boxed_1213_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object* v_as_1215_, size_t v_sz_1216_, size_t v_i_1217_, lean_object* v_b_1218_, uint8_t v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_a_1227_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; uint8_t v___x_1240_; 
v___x_1240_ = lean_usize_dec_lt(v_i_1217_, v_sz_1216_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_b_1218_);
return v___x_1241_;
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v_localDecl_1245_; lean_object* v___x_1253_; 
v_a_1242_ = lean_array_uget_borrowed(v_as_1215_, v_i_1217_);
v___x_1243_ = l_Lean_Expr_fvarId_x21(v_a_1242_);
lean_inc_ref(v___y_1221_);
lean_inc(v___x_1243_);
v___x_1253_ = l_Lean_FVarId_getDecl___redArg(v___x_1243_, v___y_1221_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = l_Lean_LocalDecl_type(v_a_1254_);
v___x_1256_ = l_Lean_Meta_AbstractNestedProofs_visit(v___x_1255_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref(v___x_1256_);
v___x_1258_ = l_Lean_LocalDecl_setType(v_a_1254_, v_a_1257_);
v___x_1259_ = l_Lean_LocalDecl_value_x3f(v___x_1258_, v___x_1240_);
if (lean_obj_tag(v___x_1259_) == 0)
{
v_localDecl_1245_ = v___x_1258_;
goto v___jp_1244_;
}
else
{
lean_object* v_val_1260_; lean_object* v___x_1261_; 
v_val_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_val_1260_);
lean_dec_ref(v___x_1259_);
v___x_1261_ = l_Lean_Meta_AbstractNestedProofs_visit(v_val_1260_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref(v___x_1261_);
v___x_1263_ = l_Lean_LocalDecl_setValue(v___x_1258_, v_a_1262_);
v_localDecl_1245_ = v___x_1263_;
goto v___jp_1244_;
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v___x_1258_);
lean_dec(v___x_1243_);
lean_dec_ref(v_b_1218_);
v_a_1264_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1261_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1261_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v_a_1254_);
lean_dec(v___x_1243_);
lean_dec_ref(v_b_1218_);
v_a_1272_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1256_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1256_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v___x_1243_);
lean_dec_ref(v_b_1218_);
v_a_1280_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1253_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1253_);
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
v___jp_1244_:
{
lean_object* v_fvarIdToDecl_1246_; lean_object* v_decls_1247_; lean_object* v_auxDeclToFullName_1248_; lean_object* v___x_1249_; 
v_fvarIdToDecl_1246_ = lean_ctor_get(v_b_1218_, 0);
v_decls_1247_ = lean_ctor_get(v_b_1218_, 1);
v_auxDeclToFullName_1248_ = lean_ctor_get(v_b_1218_, 2);
lean_inc_ref(v_b_1218_);
v___x_1249_ = lean_local_ctx_find(v_b_1218_, v___x_1243_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_dec_ref(v_localDecl_1245_);
v_a_1227_ = v_b_1218_;
goto v___jp_1226_;
}
else
{
lean_object* v_index_1250_; lean_object* v_fvarId_1251_; lean_object* v___x_1252_; 
lean_inc(v_auxDeclToFullName_1248_);
lean_inc_ref(v_decls_1247_);
lean_inc_ref(v_fvarIdToDecl_1246_);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v_b_1218_);
v_index_1250_ = lean_ctor_get(v_localDecl_1245_, 0);
lean_inc(v_index_1250_);
v_fvarId_1251_ = lean_ctor_get(v_localDecl_1245_, 1);
lean_inc_ref(v_localDecl_1245_);
lean_inc(v_fvarId_1251_);
v___x_1252_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_fvarIdToDecl_1246_, v_fvarId_1251_, v_localDecl_1245_);
v___y_1232_ = v___x_1252_;
v___y_1233_ = v_auxDeclToFullName_1248_;
v___y_1234_ = v_decls_1247_;
v___y_1235_ = v_localDecl_1245_;
v___y_1236_ = v_index_1250_;
goto v___jp_1231_;
}
}
}
v___jp_1226_:
{
size_t v___x_1228_; size_t v___x_1229_; 
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_add(v_i_1217_, v___x_1228_);
v_i_1217_ = v___x_1229_;
v_b_1218_ = v_a_1227_;
goto _start;
}
v___jp_1231_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___y_1235_);
v___x_1238_ = l_Lean_PersistentArray_set___redArg(v___y_1234_, v___y_1236_, v___x_1237_);
lean_dec(v___y_1236_);
v___x_1239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1239_, 0, v___y_1232_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
lean_ctor_set(v___x_1239_, 2, v___y_1233_);
v_a_1227_ = v___x_1239_;
goto v___jp_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object* v_xs_1288_, lean_object* v_k_1289_, uint8_t v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Meta_getLocalInstances___redArg(v___y_1292_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v_lctx_1299_; size_t v_sz_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1297_);
v_lctx_1299_ = lean_ctor_get(v___y_1292_, 2);
v_sz_1300_ = lean_array_size(v_xs_1288_);
v___x_1301_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1299_);
v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_xs_1288_, v_sz_1300_, v___x_1301_, v_lctx_1299_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1304_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref(v___x_1302_);
v___x_1304_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_a_1303_, v_a_1298_, v_k_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec_ref(v___y_1292_);
return v___x_1304_;
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v_a_1298_);
lean_dec_ref(v___y_1292_);
lean_dec_ref(v_k_1289_);
v_a_1305_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1302_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1302_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v___y_1292_);
lean_dec_ref(v_k_1289_);
v_a_1313_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1297_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1297_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object* v_xs_1321_, lean_object* v_k_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v___y_27574__boxed_1330_; lean_object* v_res_1331_; 
v___y_27574__boxed_1330_ = lean_unbox(v___y_1323_);
v_res_1331_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(v_xs_1321_, v_k_1322_, v___y_27574__boxed_1330_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec(v___y_1324_);
lean_dec_ref(v_xs_1321_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object* v___y_1332_, lean_object* v_visitBinders_1333_, lean_object* v_xs_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
uint8_t v___y_27526__boxed_1343_; uint8_t v___y_27527__boxed_1344_; lean_object* v_res_1345_; 
v___y_27526__boxed_1343_ = lean_unbox(v___y_1332_);
v___y_27527__boxed_1344_ = lean_unbox(v___y_1336_);
v_res_1345_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(v___y_27526__boxed_1343_, v_visitBinders_1333_, v_xs_1334_, v_b_1335_, v___y_27527__boxed_1344_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object* v_b_1346_, lean_object* v_xs_1347_, uint8_t v___y_1348_, uint8_t v___x_1349_, uint8_t v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1346_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; uint8_t v___x_1359_; lean_object* v___x_1360_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref(v___x_1357_);
v___x_1359_ = 1;
v___x_1360_ = l_Lean_Meta_mkForallFVars(v_xs_1347_, v_a_1358_, v___y_1348_, v___x_1349_, v___x_1349_, v___x_1359_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v___x_1360_;
}
else
{
return v___x_1357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object* v_b_1361_, lean_object* v_xs_1362_, lean_object* v___y_1363_, lean_object* v___x_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
uint8_t v___y_27560__boxed_1372_; uint8_t v___x_27561__boxed_1373_; uint8_t v___y_27562__boxed_1374_; lean_object* v_res_1375_; 
v___y_27560__boxed_1372_ = lean_unbox(v___y_1363_);
v___x_27561__boxed_1373_ = lean_unbox(v___x_1364_);
v___y_27562__boxed_1374_ = lean_unbox(v___y_1365_);
v_res_1375_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(v_b_1361_, v_xs_1362_, v___y_27560__boxed_1372_, v___x_27561__boxed_1373_, v___y_27562__boxed_1374_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v_xs_1362_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t v___y_1376_, uint8_t v___x_1377_, lean_object* v_visitBinders_1378_, lean_object* v_xs_1379_, lean_object* v_b_1380_, uint8_t v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1388_ = lean_box(v___y_1376_);
v___x_1389_ = lean_box(v___x_1377_);
lean_inc_ref(v_xs_1379_);
v___f_1390_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1390_, 0, v_b_1380_);
lean_closure_set(v___f_1390_, 1, v_xs_1379_);
lean_closure_set(v___f_1390_, 2, v___x_1388_);
lean_closure_set(v___f_1390_, 3, v___x_1389_);
v___x_1391_ = lean_box(v___y_1381_);
lean_inc(v___y_1386_);
lean_inc_ref(v___y_1385_);
lean_inc(v___y_1384_);
lean_inc_ref(v___y_1383_);
lean_inc(v___y_1382_);
v___x_1392_ = lean_apply_9(v_visitBinders_1378_, v_xs_1379_, v___f_1390_, v___x_1391_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, lean_box(0));
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object* v___y_1393_, lean_object* v___x_1394_, lean_object* v_visitBinders_1395_, lean_object* v_xs_1396_, lean_object* v_b_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
uint8_t v___y_27536__boxed_1405_; uint8_t v___x_27537__boxed_1406_; uint8_t v___y_27538__boxed_1407_; lean_object* v_res_1408_; 
v___y_27536__boxed_1405_ = lean_unbox(v___y_1393_);
v___x_27537__boxed_1406_ = lean_unbox(v___x_1394_);
v___y_27538__boxed_1407_ = lean_unbox(v___y_1398_);
v_res_1408_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(v___y_27536__boxed_1405_, v___x_27537__boxed_1406_, v_visitBinders_1395_, v_xs_1396_, v_b_1397_, v___y_27538__boxed_1407_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t v_sz_1409_, size_t v_i_1410_, lean_object* v_bs_1411_, uint8_t v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_usize_dec_lt(v_i_1410_, v_sz_1409_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_bs_1411_);
return v___x_1420_;
}
else
{
lean_object* v_v_1421_; lean_object* v___x_1422_; 
v_v_1421_ = lean_array_uget_borrowed(v_bs_1411_, v_i_1410_);
lean_inc(v_v_1421_);
v___x_1422_ = l_Lean_Meta_AbstractNestedProofs_visit(v_v_1421_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; lean_object* v_bs_x27_1425_; size_t v___x_1426_; size_t v___x_1427_; lean_object* v___x_1428_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = lean_unsigned_to_nat(0u);
v_bs_x27_1425_ = lean_array_uset(v_bs_1411_, v_i_1410_, v___x_1424_);
v___x_1426_ = ((size_t)1ULL);
v___x_1427_ = lean_usize_add(v_i_1410_, v___x_1426_);
v___x_1428_ = lean_array_uset(v_bs_x27_1425_, v_i_1410_, v_a_1423_);
v_i_1410_ = v___x_1427_;
v_bs_1411_ = v___x_1428_;
goto _start;
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v_bs_1411_);
v_a_1430_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1422_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1422_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object* v_x_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_, uint8_t v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
if (lean_obj_tag(v_x_1438_) == 5)
{
lean_object* v_fn_1448_; lean_object* v_arg_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_fn_1448_ = lean_ctor_get(v_x_1438_, 0);
lean_inc_ref(v_fn_1448_);
v_arg_1449_ = lean_ctor_get(v_x_1438_, 1);
lean_inc_ref(v_arg_1449_);
lean_dec_ref(v_x_1438_);
v___x_1450_ = lean_array_set(v_x_1439_, v_x_1440_, v_arg_1449_);
v___x_1451_ = lean_unsigned_to_nat(1u);
v___x_1452_ = lean_nat_sub(v_x_1440_, v___x_1451_);
lean_dec(v_x_1440_);
v_x_1438_ = v_fn_1448_;
v_x_1439_ = v___x_1450_;
v_x_1440_ = v___x_1452_;
goto _start;
}
else
{
lean_object* v___x_1454_; 
lean_dec(v_x_1440_);
v___x_1454_ = l_Lean_Meta_AbstractNestedProofs_visit(v_x_1438_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; size_t v_sz_1456_; size_t v___x_1457_; lean_object* v___x_1458_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref(v___x_1454_);
v_sz_1456_ = lean_array_size(v_x_1439_);
v___x_1457_ = ((size_t)0ULL);
v___x_1458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_1456_, v___x_1457_, v_x_1439_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1467_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1463_ = l_Lean_mkAppN(v_a_1455_, v_a_1459_);
lean_dec(v_a_1459_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1463_);
v___x_1465_ = v___x_1461_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_a_1455_);
v_a_1468_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1458_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1458_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_dec_ref(v_x_1439_);
return v___x_1454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object* v_e_1476_, uint8_t v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v_a_1485_; lean_object* v___y_1491_; uint8_t v___x_1493_; 
v___x_1493_ = l_Lean_Expr_isAtomic(v_e_1476_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_st_ref_get(v_a_1478_);
v___x_1495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v___x_1494_, v_e_1476_);
lean_dec(v___x_1494_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v___x_1496_; 
lean_inc_ref(v_e_1476_);
v___x_1496_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_1476_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v_visitBinders_1501_; uint8_t v___x_1502_; uint8_t v___y_1504_; uint8_t v___x_1538_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref(v___x_1496_);
v_visitBinders_1501_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed), 9, 0);
v___x_1502_ = 1;
v___x_1538_ = lean_unbox(v_a_1497_);
if (v___x_1538_ == 0)
{
uint8_t v___x_1539_; 
v___x_1539_ = lean_unbox(v_a_1497_);
lean_dec(v_a_1497_);
v___y_1504_ = v___x_1539_;
goto v___jp_1503_;
}
else
{
uint8_t v___x_1540_; 
lean_dec(v_a_1497_);
v___x_1540_ = l_Lean_Expr_hasSorry(v_e_1476_);
if (v___x_1540_ == 0)
{
lean_dec_ref(v_visitBinders_1501_);
goto v___jp_1498_;
}
else
{
if (v___x_1493_ == 0)
{
v___y_1504_ = v___x_1493_;
goto v___jp_1503_;
}
else
{
lean_dec_ref(v_visitBinders_1501_);
goto v___jp_1498_;
}
}
}
v___jp_1498_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___boxed), 8, 0);
lean_inc_ref(v_e_1476_);
v___x_1500_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_e_1476_, v_a_1477_, v___x_1499_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
v___y_1491_ = v___x_1500_;
goto v___jp_1490_;
}
v___jp_1503_:
{
switch(lean_obj_tag(v_e_1476_))
{
case 6:
{
lean_object* v___x_1505_; lean_object* v___f_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_box(v___y_1504_);
v___f_1506_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1506_, 0, v___x_1505_);
lean_closure_set(v___f_1506_, 1, v_visitBinders_1501_);
lean_inc_ref(v_e_1476_);
v___x_1507_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1476_, v___f_1506_, v___y_1504_, v___x_1502_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
v___y_1491_ = v___x_1507_;
goto v___jp_1490_;
}
case 8:
{
lean_object* v___x_1508_; lean_object* v___f_1509_; lean_object* v___x_1510_; 
v___x_1508_ = lean_box(v___y_1504_);
v___f_1509_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1509_, 0, v___x_1508_);
lean_closure_set(v___f_1509_, 1, v_visitBinders_1501_);
lean_inc_ref(v_e_1476_);
v___x_1510_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1476_, v___f_1509_, v___y_1504_, v___x_1502_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
v___y_1491_ = v___x_1510_;
goto v___jp_1490_;
}
case 7:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___f_1513_; lean_object* v___x_1514_; 
v___x_1511_ = lean_box(v___y_1504_);
v___x_1512_ = lean_box(v___x_1502_);
v___f_1513_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed), 12, 3);
lean_closure_set(v___f_1513_, 0, v___x_1511_);
lean_closure_set(v___f_1513_, 1, v___x_1512_);
lean_closure_set(v___f_1513_, 2, v_visitBinders_1501_);
lean_inc_ref(v_e_1476_);
v___x_1514_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_e_1476_, v___f_1513_, v___y_1504_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
v___y_1491_ = v___x_1514_;
goto v___jp_1490_;
}
case 10:
{
lean_object* v_data_1515_; lean_object* v_expr_1516_; lean_object* v___x_1517_; 
lean_dec_ref(v_visitBinders_1501_);
v_data_1515_ = lean_ctor_get(v_e_1476_, 0);
v_expr_1516_ = lean_ctor_get(v_e_1476_, 1);
lean_inc_ref(v_expr_1516_);
v___x_1517_ = l_Lean_Meta_AbstractNestedProofs_visit(v_expr_1516_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; size_t v___x_1519_; size_t v___x_1520_; uint8_t v___x_1521_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = lean_ptr_addr(v_expr_1516_);
v___x_1520_ = lean_ptr_addr(v_a_1518_);
v___x_1521_ = lean_usize_dec_eq(v___x_1519_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_inc(v_data_1515_);
v___x_1522_ = l_Lean_Expr_mdata___override(v_data_1515_, v_a_1518_);
v_a_1485_ = v___x_1522_;
goto v___jp_1484_;
}
else
{
lean_dec(v_a_1518_);
lean_inc_ref(v_e_1476_);
v_a_1485_ = v_e_1476_;
goto v___jp_1484_;
}
}
else
{
v___y_1491_ = v___x_1517_;
goto v___jp_1490_;
}
}
case 11:
{
lean_object* v_typeName_1523_; lean_object* v_idx_1524_; lean_object* v_struct_1525_; lean_object* v___x_1526_; 
lean_dec_ref(v_visitBinders_1501_);
v_typeName_1523_ = lean_ctor_get(v_e_1476_, 0);
v_idx_1524_ = lean_ctor_get(v_e_1476_, 1);
v_struct_1525_ = lean_ctor_get(v_e_1476_, 2);
lean_inc_ref(v_struct_1525_);
v___x_1526_ = l_Lean_Meta_AbstractNestedProofs_visit(v_struct_1525_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; size_t v___x_1528_; size_t v___x_1529_; uint8_t v___x_1530_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref(v___x_1526_);
v___x_1528_ = lean_ptr_addr(v_struct_1525_);
v___x_1529_ = lean_ptr_addr(v_a_1527_);
v___x_1530_ = lean_usize_dec_eq(v___x_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_inc(v_idx_1524_);
lean_inc(v_typeName_1523_);
v___x_1531_ = l_Lean_Expr_proj___override(v_typeName_1523_, v_idx_1524_, v_a_1527_);
v_a_1485_ = v___x_1531_;
goto v___jp_1484_;
}
else
{
lean_dec(v_a_1527_);
lean_inc_ref(v_e_1476_);
v_a_1485_ = v_e_1476_;
goto v___jp_1484_;
}
}
else
{
v___y_1491_ = v___x_1526_;
goto v___jp_1490_;
}
}
case 5:
{
lean_object* v_dummy_1532_; lean_object* v_nargs_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec_ref(v_visitBinders_1501_);
v_dummy_1532_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_1533_ = l_Lean_Expr_getAppNumArgs(v_e_1476_);
lean_inc(v_nargs_1533_);
v___x_1534_ = lean_mk_array(v_nargs_1533_, v_dummy_1532_);
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_nat_sub(v_nargs_1533_, v___x_1535_);
lean_dec(v_nargs_1533_);
lean_inc_ref(v_e_1476_);
v___x_1537_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_e_1476_, v___x_1534_, v___x_1536_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
v___y_1491_ = v___x_1537_;
goto v___jp_1490_;
}
default: 
{
lean_dec_ref(v_visitBinders_1501_);
lean_inc_ref(v_e_1476_);
v_a_1485_ = v_e_1476_;
goto v___jp_1484_;
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v_e_1476_);
v_a_1541_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1496_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1496_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v_val_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec_ref(v_e_1476_);
v_val_1549_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1495_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_val_1549_);
lean_dec(v___x_1495_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 0);
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_val_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v_e_1476_);
return v___x_1557_;
}
v___jp_1484_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = lean_st_ref_take(v_a_1478_);
lean_inc_ref(v_a_1485_);
v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v___x_1486_, v_e_1476_, v_a_1485_);
v___x_1488_ = lean_st_ref_set(v_a_1478_, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_a_1485_);
return v___x_1489_;
}
v___jp_1490_:
{
if (lean_obj_tag(v___y_1491_) == 0)
{
lean_object* v_a_1492_; 
v_a_1492_ = lean_ctor_get(v___y_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref(v___y_1491_);
v_a_1485_ = v_a_1492_;
goto v___jp_1484_;
}
else
{
lean_dec_ref(v_e_1476_);
return v___y_1491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object* v_b_1558_, lean_object* v_xs_1559_, uint8_t v___y_1560_, uint8_t v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1558_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1568_);
v___x_1570_ = 1;
v___x_1571_ = l_Lean_Meta_mkLambdaFVars(v_xs_1559_, v_a_1569_, v___y_1560_, v___y_1560_, v___y_1560_, v___y_1560_, v___x_1570_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
return v___x_1571_;
}
else
{
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object* v_b_1572_, lean_object* v_xs_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
uint8_t v___y_27547__boxed_1582_; uint8_t v___y_27548__boxed_1583_; lean_object* v_res_1584_; 
v___y_27547__boxed_1582_ = lean_unbox(v___y_1574_);
v___y_27548__boxed_1583_ = lean_unbox(v___y_1575_);
v_res_1584_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(v_b_1572_, v_xs_1573_, v___y_27547__boxed_1582_, v___y_27548__boxed_1583_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v_xs_1573_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t v___y_1585_, lean_object* v_visitBinders_1586_, lean_object* v_xs_1587_, lean_object* v_b_1588_, uint8_t v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; lean_object* v___f_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1596_ = lean_box(v___y_1585_);
lean_inc_ref(v_xs_1587_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1597_, 0, v_b_1588_);
lean_closure_set(v___f_1597_, 1, v_xs_1587_);
lean_closure_set(v___f_1597_, 2, v___x_1596_);
v___x_1598_ = lean_box(v___y_1589_);
lean_inc(v___y_1594_);
lean_inc_ref(v___y_1593_);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
v___x_1599_ = lean_apply_9(v_visitBinders_1586_, v_xs_1587_, v___f_1597_, v___x_1598_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, lean_box(0));
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object* v_sz_1600_, lean_object* v_i_1601_, lean_object* v_bs_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
size_t v_sz_boxed_1610_; size_t v_i_boxed_1611_; uint8_t v___y_27591__boxed_1612_; lean_object* v_res_1613_; 
v_sz_boxed_1610_ = lean_unbox_usize(v_sz_1600_);
lean_dec(v_sz_1600_);
v_i_boxed_1611_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v___y_27591__boxed_1612_ = lean_unbox(v___y_1603_);
v_res_1613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_boxed_1610_, v_i_boxed_1611_, v_bs_1602_, v___y_27591__boxed_1612_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v___y_27612__boxed_1624_; lean_object* v_res_1625_; 
v___y_27612__boxed_1624_ = lean_unbox(v___y_1617_);
v_res_1625_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_x_1614_, v_x_1615_, v_x_1616_, v___y_27612__boxed_1624_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object* v_as_1626_, lean_object* v_sz_1627_, lean_object* v_i_1628_, lean_object* v_b_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
size_t v_sz_boxed_1637_; size_t v_i_boxed_1638_; uint8_t v___y_27635__boxed_1639_; lean_object* v_res_1640_; 
v_sz_boxed_1637_ = lean_unbox_usize(v_sz_1627_);
lean_dec(v_sz_1627_);
v_i_boxed_1638_ = lean_unbox_usize(v_i_1628_);
lean_dec(v_i_1628_);
v___y_27635__boxed_1639_ = lean_unbox(v___y_1630_);
v_res_1640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_as_1626_, v_sz_boxed_1637_, v_i_boxed_1638_, v_b_1629_, v___y_27635__boxed_1639_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v_as_1626_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object* v_00_u03b2_1641_, lean_object* v_m_1642_, lean_object* v_a_1643_, lean_object* v_b_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_m_1642_, v_a_1643_, v_b_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object* v_00_u03b2_1646_, lean_object* v_m_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_1647_, v_a_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object* v_00_u03b2_1650_, lean_object* v_m_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_00_u03b2_1650_, v_m_1651_, v_a_1652_);
lean_dec_ref(v_a_1652_);
lean_dec_ref(v_m_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object* v_00_u03b2_1654_, lean_object* v_x_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_x_1655_, v_x_1656_, v_x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object* v_00_u03b2_1659_, lean_object* v_a_1660_, lean_object* v_x_1661_){
_start:
{
uint8_t v___x_1662_; 
v___x_1662_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1660_, v_x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1663_, lean_object* v_a_1664_, lean_object* v_x_1665_){
_start:
{
uint8_t v_res_1666_; lean_object* v_r_1667_; 
v_res_1666_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(v_00_u03b2_1663_, v_a_1664_, v_x_1665_);
lean_dec(v_x_1665_);
lean_dec_ref(v_a_1664_);
v_r_1667_ = lean_box(v_res_1666_);
return v_r_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2(lean_object* v_00_u03b2_1668_, lean_object* v_data_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(v_data_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3(lean_object* v_00_u03b2_1671_, lean_object* v_a_1672_, lean_object* v_b_1673_, lean_object* v_x_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1672_, v_b_1673_, v_x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(lean_object* v_00_u03b2_1676_, lean_object* v_a_1677_, lean_object* v_x_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_1677_, v_x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1680_, lean_object* v_a_1681_, lean_object* v_x_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(v_00_u03b2_1680_, v_a_1681_, v_x_1682_);
lean_dec(v_x_1682_);
lean_dec_ref(v_a_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b1_1684_, lean_object* v_x_1685_, uint8_t v_isExporting_1686_, uint8_t v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_1685_, v_isExporting_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_x_1696_, lean_object* v_isExporting_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
uint8_t v_isExporting_boxed_1705_; uint8_t v___y_28214__boxed_1706_; lean_object* v_res_1707_; 
v_isExporting_boxed_1705_ = lean_unbox(v_isExporting_1697_);
v___y_28214__boxed_1706_ = lean_unbox(v___y_1698_);
v_res_1707_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(v_00_u03b1_1695_, v_x_1696_, v_isExporting_boxed_1705_, v___y_28214__boxed_1706_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(lean_object* v_00_u03b1_1708_, lean_object* v_x_1709_, uint8_t v_when_1710_, uint8_t v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_1709_, v_when_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_x_1720_, lean_object* v_when_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
uint8_t v_when_boxed_1729_; uint8_t v___y_28237__boxed_1730_; lean_object* v_res_1731_; 
v_when_boxed_1729_ = lean_unbox(v_when_1721_);
v___y_28237__boxed_1730_ = lean_unbox(v___y_1722_);
v_res_1731_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(v_00_u03b1_1719_, v_x_1720_, v_when_boxed_1729_, v___y_28237__boxed_1730_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9(lean_object* v_00_u03b2_1732_, lean_object* v_x_1733_, size_t v_x_1734_, size_t v_x_1735_, lean_object* v_x_1736_, lean_object* v_x_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_1733_, v_x_1734_, v_x_1735_, v_x_1736_, v_x_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_, lean_object* v_x_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_){
_start:
{
size_t v_x_28261__boxed_1745_; size_t v_x_28262__boxed_1746_; lean_object* v_res_1747_; 
v_x_28261__boxed_1745_ = lean_unbox_usize(v_x_1741_);
lean_dec(v_x_1741_);
v_x_28262__boxed_1746_ = lean_unbox_usize(v_x_1742_);
lean_dec(v_x_1742_);
v_res_1747_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9(v_00_u03b2_1739_, v_x_1740_, v_x_28261__boxed_1745_, v_x_28262__boxed_1746_, v_x_1743_, v_x_1744_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1748_, lean_object* v_i_1749_, lean_object* v_source_1750_, lean_object* v_target_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(v_i_1749_, v_source_1750_, v_target_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15(lean_object* v_00_u03b2_1753_, lean_object* v_n_1754_, lean_object* v_k_1755_, lean_object* v_v_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(v_n_1754_, v_k_1755_, v_v_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16(lean_object* v_00_u03b2_1758_, size_t v_depth_1759_, lean_object* v_keys_1760_, lean_object* v_vals_1761_, lean_object* v_heq_1762_, lean_object* v_i_1763_, lean_object* v_entries_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_depth_1759_, v_keys_1760_, v_vals_1761_, v_i_1763_, v_entries_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1766_, lean_object* v_depth_1767_, lean_object* v_keys_1768_, lean_object* v_vals_1769_, lean_object* v_heq_1770_, lean_object* v_i_1771_, lean_object* v_entries_1772_){
_start:
{
size_t v_depth_boxed_1773_; lean_object* v_res_1774_; 
v_depth_boxed_1773_ = lean_unbox_usize(v_depth_1767_);
lean_dec(v_depth_1767_);
v_res_1774_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16(v_00_u03b2_1766_, v_depth_boxed_1773_, v_keys_1768_, v_vals_1769_, v_heq_1770_, v_i_1771_, v_entries_1772_);
lean_dec_ref(v_vals_1769_);
lean_dec_ref(v_keys_1768_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1775_, lean_object* v_x_1776_, lean_object* v_x_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(v_x_1776_, v_x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19(lean_object* v_00_u03b2_1779_, lean_object* v_x_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_, lean_object* v_x_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(v_x_1780_, v_x_1781_, v_x_1782_, v_x_1783_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__0(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_box(0);
v___x_1786_ = lean_unsigned_to_nat(16u);
v___x_1787_ = lean_mk_array(v___x_1786_, v___x_1785_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__1(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__0, &l_Lean_Meta_abstractNestedProofs___closed__0_once, _init_l_Lean_Meta_abstractNestedProofs___closed__0);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v___x_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs(lean_object* v_e_1791_, uint8_t v_cache_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v___x_1798_; 
lean_inc_ref(v_e_1791_);
v___x_1798_ = l_Lean_Meta_isProof(v_e_1791_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1819_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1819_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1819_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_unbox(v_a_1799_);
lean_dec(v_a_1799_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_del_object(v___x_1801_);
v___x_1804_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__1, &l_Lean_Meta_abstractNestedProofs___closed__1_once, _init_l_Lean_Meta_abstractNestedProofs___closed__1);
v___x_1805_ = lean_st_mk_ref(v___x_1804_);
v___x_1806_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1791_, v_cache_1792_, v___x_1805_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1815_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_st_ref_get(v___x_1805_);
lean_dec(v___x_1805_);
lean_dec(v___x_1811_);
if (v_isShared_1810_ == 0)
{
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1807_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
lean_dec(v___x_1805_);
return v___x_1806_;
}
}
else
{
lean_object* v___x_1817_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v_e_1791_);
v___x_1817_ = v___x_1801_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_e_1791_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec_ref(v_e_1791_);
v_a_1820_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1798_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1798_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object* v_e_1828_, lean_object* v_cache_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
uint8_t v_cache_boxed_1835_; lean_object* v_res_1836_; 
v_cache_boxed_1835_ = lean_unbox(v_cache_1829_);
v_res_1836_ = l_Lean_Meta_abstractNestedProofs(v_e_1828_, v_cache_boxed_1835_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
return v_res_1836_;
}
}
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_AbstractNestedProofs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
