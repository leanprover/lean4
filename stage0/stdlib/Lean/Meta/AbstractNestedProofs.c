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
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "abstract nested proofs"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_visit___closed__0 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value;
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
uint8_t v_a_4326__boxed_143_; uint8_t v___y_4327__boxed_144_; size_t v_i_boxed_145_; size_t v_stop_boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v_a_4326__boxed_143_ = lean_unbox(v_a_138_);
v___y_4327__boxed_144_ = lean_unbox(v___y_139_);
v_i_boxed_145_ = lean_unbox_usize(v_i_141_);
lean_dec(v_i_141_);
v_stop_boxed_146_ = lean_unbox_usize(v_stop_142_);
lean_dec(v_stop_142_);
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_4326__boxed_143_, v___y_4327__boxed_144_, v_as_140_, v_i_boxed_145_, v_stop_boxed_146_);
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
uint8_t v_a_4352__boxed_192_; uint8_t v___x_4353__boxed_193_; lean_object* v_res_194_; 
v_a_4352__boxed_192_ = lean_unbox(v_a_185_);
v___x_4353__boxed_193_ = lean_unbox(v___x_186_);
v_res_194_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_a_4352__boxed_192_, v___x_4353__boxed_193_, v___x_187_, v_x_188_, v_x_189_, v_x_190_);
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
lean_object* v___x_249_; lean_object* v_env_250_; lean_object* v_nextMacroScope_251_; lean_object* v_ngen_252_; lean_object* v_auxDeclNGen_253_; lean_object* v_traceState_254_; lean_object* v_messages_255_; lean_object* v_infoState_256_; lean_object* v_snapshotTasks_257_; lean_object* v_newDecls_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_283_; 
v___x_249_ = lean_st_ref_take(v___y_242_);
v_env_250_ = lean_ctor_get(v___x_249_, 0);
v_nextMacroScope_251_ = lean_ctor_get(v___x_249_, 1);
v_ngen_252_ = lean_ctor_get(v___x_249_, 2);
v_auxDeclNGen_253_ = lean_ctor_get(v___x_249_, 3);
v_traceState_254_ = lean_ctor_get(v___x_249_, 4);
v_messages_255_ = lean_ctor_get(v___x_249_, 6);
v_infoState_256_ = lean_ctor_get(v___x_249_, 7);
v_snapshotTasks_257_ = lean_ctor_get(v___x_249_, 8);
v_newDecls_258_ = lean_ctor_get(v___x_249_, 9);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v___x_249_, 5);
lean_dec(v_unused_284_);
v___x_260_ = v___x_249_;
v_isShared_261_ = v_isSharedCheck_283_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_newDecls_258_);
lean_inc(v_snapshotTasks_257_);
lean_inc(v_infoState_256_);
lean_inc(v_messages_255_);
lean_inc(v_traceState_254_);
lean_inc(v_auxDeclNGen_253_);
lean_inc(v_ngen_252_);
lean_inc(v_nextMacroScope_251_);
lean_inc(v_env_250_);
lean_dec(v___x_249_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_283_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = l_Lean_Environment_setExporting(v_env_250_, v_isExporting_243_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 5, v___x_244_);
lean_ctor_set(v___x_260_, 0, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_nextMacroScope_251_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_ngen_252_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_auxDeclNGen_253_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_traceState_254_);
lean_ctor_set(v_reuseFailAlloc_282_, 5, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_282_, 6, v_messages_255_);
lean_ctor_set(v_reuseFailAlloc_282_, 7, v_infoState_256_);
lean_ctor_set(v_reuseFailAlloc_282_, 8, v_snapshotTasks_257_);
lean_ctor_set(v_reuseFailAlloc_282_, 9, v_newDecls_258_);
v___x_264_ = v_reuseFailAlloc_282_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v_mctx_267_; lean_object* v_zetaDeltaFVarIds_268_; lean_object* v_postponed_269_; lean_object* v_diag_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_280_; 
v___x_265_ = lean_st_ref_set(v___y_242_, v___x_264_);
v___x_266_ = lean_st_ref_take(v___y_245_);
v_mctx_267_ = lean_ctor_get(v___x_266_, 0);
v_zetaDeltaFVarIds_268_ = lean_ctor_get(v___x_266_, 2);
v_postponed_269_ = lean_ctor_get(v___x_266_, 3);
v_diag_270_ = lean_ctor_get(v___x_266_, 4);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v___x_266_, 1);
lean_dec(v_unused_281_);
v___x_272_ = v___x_266_;
v_isShared_273_ = v_isSharedCheck_280_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_diag_270_);
lean_inc(v_postponed_269_);
lean_inc(v_zetaDeltaFVarIds_268_);
lean_inc(v_mctx_267_);
lean_dec(v___x_266_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_280_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v___x_246_);
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_mctx_267_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_zetaDeltaFVarIds_268_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_postponed_269_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_diag_270_);
v___x_275_ = v_reuseFailAlloc_279_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_st_ref_set(v___y_245_, v___x_275_);
v___x_277_ = lean_box(0);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_285_, lean_object* v_isExporting_286_, lean_object* v___x_287_, lean_object* v___y_288_, lean_object* v___x_289_, lean_object* v_a_x3f_290_, lean_object* v___y_291_){
_start:
{
uint8_t v_isExporting_boxed_292_; lean_object* v_res_293_; 
v_isExporting_boxed_292_ = lean_unbox(v_isExporting_286_);
v_res_293_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_285_, v_isExporting_boxed_292_, v___x_287_, v___y_288_, v___x_289_, v_a_x3f_290_);
lean_dec(v_a_x3f_290_);
lean_dec(v___y_288_);
lean_dec(v___y_285_);
return v_res_293_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_294_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1);
v___x_300_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
lean_ctor_set(v___x_300_, 2, v___x_299_);
lean_ctor_set(v___x_300_, 3, v___x_299_);
lean_ctor_set(v___x_300_, 4, v___x_299_);
lean_ctor_set(v___x_300_, 5, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(lean_object* v_x_301_, uint8_t v_isExporting_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; lean_object* v_env_309_; uint8_t v_isExporting_310_; lean_object* v___x_311_; lean_object* v_env_312_; lean_object* v_nextMacroScope_313_; lean_object* v_ngen_314_; lean_object* v_auxDeclNGen_315_; lean_object* v_traceState_316_; lean_object* v_messages_317_; lean_object* v_infoState_318_; lean_object* v_snapshotTasks_319_; lean_object* v_newDecls_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_374_; 
v___x_308_ = lean_st_ref_get(v___y_306_);
v_env_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref(v_env_309_);
lean_dec(v___x_308_);
v_isExporting_310_ = lean_ctor_get_uint8(v_env_309_, sizeof(void*)*8);
lean_dec_ref(v_env_309_);
v___x_311_ = lean_st_ref_take(v___y_306_);
v_env_312_ = lean_ctor_get(v___x_311_, 0);
v_nextMacroScope_313_ = lean_ctor_get(v___x_311_, 1);
v_ngen_314_ = lean_ctor_get(v___x_311_, 2);
v_auxDeclNGen_315_ = lean_ctor_get(v___x_311_, 3);
v_traceState_316_ = lean_ctor_get(v___x_311_, 4);
v_messages_317_ = lean_ctor_get(v___x_311_, 6);
v_infoState_318_ = lean_ctor_get(v___x_311_, 7);
v_snapshotTasks_319_ = lean_ctor_get(v___x_311_, 8);
v_newDecls_320_ = lean_ctor_get(v___x_311_, 9);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v___x_311_, 5);
lean_dec(v_unused_375_);
v___x_322_ = v___x_311_;
v_isShared_323_ = v_isSharedCheck_374_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_newDecls_320_);
lean_inc(v_snapshotTasks_319_);
lean_inc(v_infoState_318_);
lean_inc(v_messages_317_);
lean_inc(v_traceState_316_);
lean_inc(v_auxDeclNGen_315_);
lean_inc(v_ngen_314_);
lean_inc(v_nextMacroScope_313_);
lean_inc(v_env_312_);
lean_dec(v___x_311_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_374_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_324_ = l_Lean_Environment_setExporting(v_env_312_, v_isExporting_302_);
v___x_325_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 5, v___x_325_);
lean_ctor_set(v___x_322_, 0, v___x_324_);
v___x_327_ = v___x_322_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_nextMacroScope_313_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_ngen_314_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_auxDeclNGen_315_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_traceState_316_);
lean_ctor_set(v_reuseFailAlloc_373_, 5, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_373_, 6, v_messages_317_);
lean_ctor_set(v_reuseFailAlloc_373_, 7, v_infoState_318_);
lean_ctor_set(v_reuseFailAlloc_373_, 8, v_snapshotTasks_319_);
lean_ctor_set(v_reuseFailAlloc_373_, 9, v_newDecls_320_);
v___x_327_ = v_reuseFailAlloc_373_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v_mctx_330_; lean_object* v_zetaDeltaFVarIds_331_; lean_object* v_postponed_332_; lean_object* v_diag_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_371_; 
v___x_328_ = lean_st_ref_set(v___y_306_, v___x_327_);
v___x_329_ = lean_st_ref_take(v___y_304_);
v_mctx_330_ = lean_ctor_get(v___x_329_, 0);
v_zetaDeltaFVarIds_331_ = lean_ctor_get(v___x_329_, 2);
v_postponed_332_ = lean_ctor_get(v___x_329_, 3);
v_diag_333_ = lean_ctor_get(v___x_329_, 4);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_329_, 1);
lean_dec(v_unused_372_);
v___x_335_ = v___x_329_;
v_isShared_336_ = v_isSharedCheck_371_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_diag_333_);
lean_inc(v_postponed_332_);
lean_inc(v_zetaDeltaFVarIds_331_);
lean_inc(v_mctx_330_);
lean_dec(v___x_329_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_371_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v___x_337_);
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_mctx_330_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_zetaDeltaFVarIds_331_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_postponed_332_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v_diag_333_);
v___x_339_ = v_reuseFailAlloc_370_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_340_; lean_object* v_r_341_; 
v___x_340_ = lean_st_ref_set(v___y_304_, v___x_339_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
v_r_341_ = lean_apply_5(v_x_301_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, lean_box(0));
if (lean_obj_tag(v_r_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_358_; 
v_a_342_ = lean_ctor_get(v_r_341_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v_r_341_);
if (v_isSharedCheck_358_ == 0)
{
v___x_344_ = v_r_341_;
v_isShared_345_ = v_isSharedCheck_358_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v_r_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_358_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
lean_inc(v_a_342_);
if (v_isShared_345_ == 0)
{
lean_ctor_set_tag(v___x_344_, 1);
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_357_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
v___x_348_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_306_, v_isExporting_310_, v___x_325_, v___y_304_, v___x_337_, v___x_347_);
lean_dec_ref(v___x_347_);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; 
v_unused_356_ = lean_ctor_get(v___x_348_, 0);
lean_dec(v_unused_356_);
v___x_350_ = v___x_348_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_dec(v___x_348_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v_a_342_);
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_342_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
v_a_359_ = lean_ctor_get(v_r_341_, 0);
lean_inc(v_a_359_);
lean_dec_ref(v_r_341_);
v___x_360_ = lean_box(0);
v___x_361_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_306_, v_isExporting_310_, v___x_325_, v___y_304_, v___x_337_, v___x_360_);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_361_, 0);
lean_dec(v_unused_369_);
v___x_363_ = v___x_361_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_dec(v___x_361_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set_tag(v___x_363_, 1);
lean_ctor_set(v___x_363_, 0, v_a_359_);
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_359_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___boxed(lean_object* v_x_376_, lean_object* v_isExporting_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
uint8_t v_isExporting_boxed_383_; lean_object* v_res_384_; 
v_isExporting_boxed_383_ = lean_unbox(v_isExporting_377_);
v_res_384_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_376_, v_isExporting_boxed_383_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object* v_x_385_, uint8_t v_when_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
if (v_when_386_ == 0)
{
lean_object* v___x_392_; 
lean_inc(v___y_390_);
lean_inc_ref(v___y_389_);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
v___x_392_ = lean_apply_5(v_x_385_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, lean_box(0));
return v___x_392_;
}
else
{
uint8_t v___x_393_; lean_object* v___x_394_; 
v___x_393_ = 0;
v___x_394_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_385_, v___x_393_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object* v_x_395_, lean_object* v_when_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
uint8_t v_when_boxed_402_; lean_object* v_res_403_; 
v_when_boxed_402_ = lean_unbox(v_when_396_);
v_res_403_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_395_, v_when_boxed_402_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object* v_e_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; lean_object* v_env_411_; lean_object* v___f_412_; uint8_t v___x_413_; lean_object* v___x_414_; 
v___x_410_ = lean_st_ref_get(v_a_408_);
v_env_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc_ref(v_env_411_);
lean_dec(v___x_410_);
v___f_412_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed), 7, 2);
lean_closure_set(v___f_412_, 0, v_e_404_);
lean_closure_set(v___f_412_, 1, v_env_411_);
v___x_413_ = 1;
v___x_414_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v___f_412_, v___x_413_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object* v_e_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(uint8_t v_a_422_, uint8_t v___x_423_, lean_object* v___x_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_x_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_a_422_, v___x_423_, v___x_424_, v_x_425_, v_x_426_, v_x_427_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object* v_a_434_, lean_object* v___x_435_, lean_object* v___x_436_, lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
uint8_t v_a_4763__boxed_445_; uint8_t v___x_4764__boxed_446_; lean_object* v_res_447_; 
v_a_4763__boxed_445_ = lean_unbox(v_a_434_);
v___x_4764__boxed_446_ = lean_unbox(v___x_435_);
v_res_447_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(v_a_4763__boxed_445_, v___x_4764__boxed_446_, v___x_436_, v_x_437_, v_x_438_, v_x_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(lean_object* v_00_u03b1_448_, lean_object* v_x_449_, uint8_t v_isExporting_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_449_, v_isExporting_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___boxed(lean_object* v_00_u03b1_457_, lean_object* v_x_458_, lean_object* v_isExporting_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
uint8_t v_isExporting_boxed_465_; lean_object* v_res_466_; 
v_isExporting_boxed_465_ = lean_unbox(v_isExporting_459_);
v_res_466_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(v_00_u03b1_457_, v_x_458_, v_isExporting_boxed_465_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object* v_00_u03b1_467_, lean_object* v_x_468_, uint8_t v_when_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_468_, v_when_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object* v_00_u03b1_476_, lean_object* v_x_477_, lean_object* v_when_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
uint8_t v_when_boxed_484_; lean_object* v_res_485_; 
v_when_boxed_484_ = lean_unbox(v_when_478_);
v_res_485_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(v_00_u03b1_476_, v_x_477_, v_when_boxed_484_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(lean_object* v_x_486_, uint8_t v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_box(v___y_487_);
lean_inc(v___y_488_);
v___x_495_ = lean_apply_7(v_x_486_, v___x_494_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, lean_box(0));
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed(lean_object* v_x_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
uint8_t v___y_29369__boxed_504_; lean_object* v_res_505_; 
v___y_29369__boxed_504_ = lean_unbox(v___y_497_);
v_res_505_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(v_x_496_, v___y_29369__boxed_504_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_498_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(lean_object* v_lctx_506_, lean_object* v_localInsts_507_, lean_object* v_x_508_, uint8_t v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; lean_object* v___f_517_; lean_object* v___x_518_; 
v___x_516_ = lean_box(v___y_509_);
lean_inc(v___y_510_);
v___f_517_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_517_, 0, v_x_508_);
lean_closure_set(v___f_517_, 1, v___x_516_);
lean_closure_set(v___f_517_, 2, v___y_510_);
v___x_518_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_506_, v_localInsts_507_, v___f_517_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
if (lean_obj_tag(v___x_518_) == 0)
{
return v___x_518_;
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___boxed(lean_object* v_lctx_527_, lean_object* v_localInsts_528_, lean_object* v_x_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
uint8_t v___y_29394__boxed_537_; lean_object* v_res_538_; 
v___y_29394__boxed_537_ = lean_unbox(v___y_530_);
v_res_538_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_lctx_527_, v_localInsts_528_, v_x_529_, v___y_29394__boxed_537_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object* v_00_u03b1_539_, lean_object* v_lctx_540_, lean_object* v_localInsts_541_, lean_object* v_x_542_, uint8_t v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_lctx_540_, v_localInsts_541_, v_x_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object* v_00_u03b1_551_, lean_object* v_lctx_552_, lean_object* v_localInsts_553_, lean_object* v_x_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v___y_29438__boxed_562_; lean_object* v_res_563_; 
v___y_29438__boxed_562_ = lean_unbox(v___y_555_);
v_res_563_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_00_u03b1_551_, v_lctx_552_, v_localInsts_553_, v_x_554_, v___y_29438__boxed_562_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(lean_object* v_k_564_, uint8_t v___y_565_, lean_object* v___y_566_, lean_object* v_b_567_, lean_object* v_c_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_box(v___y_565_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
lean_inc(v___y_570_);
lean_inc_ref(v___y_569_);
lean_inc(v___y_566_);
v___x_575_ = lean_apply_9(v_k_564_, v_b_567_, v_c_568_, v___x_574_, v___y_566_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, lean_box(0));
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed(lean_object* v_k_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v_b_579_, lean_object* v_c_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
uint8_t v___y_29461__boxed_586_; lean_object* v_res_587_; 
v___y_29461__boxed_586_ = lean_unbox(v___y_577_);
v_res_587_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(v_k_576_, v___y_29461__boxed_586_, v___y_578_, v_b_579_, v_c_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_578_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object* v_e_588_, lean_object* v_k_589_, uint8_t v_cleanupAnnotations_590_, uint8_t v_preserveNondepLet_591_, uint8_t v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; lean_object* v___f_600_; uint8_t v___x_601_; uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_599_ = lean_box(v___y_592_);
lean_inc(v___y_593_);
v___f_600_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_600_, 0, v_k_589_);
lean_closure_set(v___f_600_, 1, v___x_599_);
lean_closure_set(v___f_600_, 2, v___y_593_);
v___x_601_ = 1;
v___x_602_ = 0;
v___x_603_ = lean_box(0);
v___x_604_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_588_, v___x_601_, v___x_601_, v_preserveNondepLet_591_, v___x_602_, v___x_603_, v___f_600_, v_cleanupAnnotations_590_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_604_) == 0)
{
return v___x_604_;
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object* v_e_613_, lean_object* v_k_614_, lean_object* v_cleanupAnnotations_615_, lean_object* v_preserveNondepLet_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_624_; uint8_t v_preserveNondepLet_boxed_625_; uint8_t v___y_29486__boxed_626_; lean_object* v_res_627_; 
v_cleanupAnnotations_boxed_624_ = lean_unbox(v_cleanupAnnotations_615_);
v_preserveNondepLet_boxed_625_ = lean_unbox(v_preserveNondepLet_616_);
v___y_29486__boxed_626_ = lean_unbox(v___y_617_);
v_res_627_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_613_, v_k_614_, v_cleanupAnnotations_boxed_624_, v_preserveNondepLet_boxed_625_, v___y_29486__boxed_626_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object* v_00_u03b1_628_, lean_object* v_e_629_, lean_object* v_k_630_, uint8_t v_cleanupAnnotations_631_, uint8_t v_preserveNondepLet_632_, uint8_t v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_629_, v_k_630_, v_cleanupAnnotations_631_, v_preserveNondepLet_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object* v_00_u03b1_641_, lean_object* v_e_642_, lean_object* v_k_643_, lean_object* v_cleanupAnnotations_644_, lean_object* v_preserveNondepLet_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_653_; uint8_t v_preserveNondepLet_boxed_654_; uint8_t v___y_29536__boxed_655_; lean_object* v_res_656_; 
v_cleanupAnnotations_boxed_653_ = lean_unbox(v_cleanupAnnotations_644_);
v_preserveNondepLet_boxed_654_ = lean_unbox(v_preserveNondepLet_645_);
v___y_29536__boxed_655_ = lean_unbox(v___y_646_);
v_res_656_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(v_00_u03b1_641_, v_e_642_, v_k_643_, v_cleanupAnnotations_boxed_653_, v_preserveNondepLet_boxed_654_, v___y_29536__boxed_655_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(lean_object* v_type_657_, lean_object* v_k_658_, uint8_t v_cleanupAnnotations_659_, uint8_t v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; lean_object* v___f_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_667_ = lean_box(v___y_660_);
lean_inc(v___y_661_);
v___f_668_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_668_, 0, v_k_658_);
lean_closure_set(v___f_668_, 1, v___x_667_);
lean_closure_set(v___f_668_, 2, v___y_661_);
v___x_669_ = 0;
v___x_670_ = lean_box(0);
v___x_671_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_669_, v___x_670_, v_type_657_, v___f_668_, v_cleanupAnnotations_659_, v___x_669_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_671_) == 0)
{
return v___x_671_;
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___boxed(lean_object* v_type_680_, lean_object* v_k_681_, lean_object* v_cleanupAnnotations_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_690_; uint8_t v___y_29559__boxed_691_; lean_object* v_res_692_; 
v_cleanupAnnotations_boxed_690_ = lean_unbox(v_cleanupAnnotations_682_);
v___y_29559__boxed_691_ = lean_unbox(v___y_683_);
v_res_692_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_680_, v_k_681_, v_cleanupAnnotations_boxed_690_, v___y_29559__boxed_691_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object* v_00_u03b1_693_, lean_object* v_type_694_, lean_object* v_k_695_, uint8_t v_cleanupAnnotations_696_, uint8_t v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_694_, v_k_695_, v_cleanupAnnotations_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object* v_00_u03b1_705_, lean_object* v_type_706_, lean_object* v_k_707_, lean_object* v_cleanupAnnotations_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_716_; uint8_t v___y_29607__boxed_717_; lean_object* v_res_718_; 
v_cleanupAnnotations_boxed_716_ = lean_unbox(v_cleanupAnnotations_708_);
v___y_29607__boxed_717_ = lean_unbox(v___y_709_);
v_res_718_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_00_u03b1_705_, v_type_706_, v_k_707_, v_cleanupAnnotations_boxed_716_, v___y_29607__boxed_717_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_x_722_){
_start:
{
lean_object* v_ks_723_; lean_object* v_vs_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_748_; 
v_ks_723_ = lean_ctor_get(v_x_719_, 0);
v_vs_724_ = lean_ctor_get(v_x_719_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_719_);
if (v_isSharedCheck_748_ == 0)
{
v___x_726_ = v_x_719_;
v_isShared_727_ = v_isSharedCheck_748_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_vs_724_);
lean_inc(v_ks_723_);
lean_dec(v_x_719_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_748_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_array_get_size(v_ks_723_);
v___x_729_ = lean_nat_dec_lt(v_x_720_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
lean_dec(v_x_720_);
v___x_730_ = lean_array_push(v_ks_723_, v_x_721_);
v___x_731_ = lean_array_push(v_vs_724_, v_x_722_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_731_);
lean_ctor_set(v___x_726_, 0, v___x_730_);
v___x_733_ = v___x_726_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
else
{
lean_object* v_k_x27_735_; uint8_t v___x_736_; 
v_k_x27_735_ = lean_array_fget_borrowed(v_ks_723_, v_x_720_);
v___x_736_ = l_Lean_instBEqFVarId_beq(v_x_721_, v_k_x27_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_738_; 
if (v_isShared_727_ == 0)
{
v___x_738_ = v___x_726_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_ks_723_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_vs_724_);
v___x_738_ = v_reuseFailAlloc_742_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = lean_nat_add(v_x_720_, v___x_739_);
lean_dec(v_x_720_);
v_x_719_ = v___x_738_;
v_x_720_ = v___x_740_;
goto _start;
}
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_743_ = lean_array_fset(v_ks_723_, v_x_720_, v_x_721_);
v___x_744_ = lean_array_fset(v_vs_724_, v_x_720_, v_x_722_);
lean_dec(v_x_720_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_744_);
lean_ctor_set(v___x_726_, 0, v___x_743_);
v___x_746_ = v___x_726_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(lean_object* v_n_749_, lean_object* v_k_750_, lean_object* v_v_751_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(v_n_749_, v___x_752_, v_k_750_, v_v_751_);
return v___x_753_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0(void){
_start:
{
size_t v___x_754_; size_t v___x_755_; size_t v___x_756_; 
v___x_754_ = ((size_t)5ULL);
v___x_755_ = ((size_t)1ULL);
v___x_756_ = lean_usize_shift_left(v___x_755_, v___x_754_);
return v___x_756_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1(void){
_start:
{
size_t v___x_757_; size_t v___x_758_; size_t v___x_759_; 
v___x_757_ = ((size_t)1ULL);
v___x_758_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0);
v___x_759_ = lean_usize_sub(v___x_758_, v___x_757_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(lean_object* v_x_761_, size_t v_x_762_, size_t v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
lean_object* v_es_766_; size_t v___x_767_; size_t v___x_768_; size_t v___x_769_; size_t v___x_770_; lean_object* v_j_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_es_766_ = lean_ctor_get(v_x_761_, 0);
v___x_767_ = ((size_t)5ULL);
v___x_768_ = ((size_t)1ULL);
v___x_769_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__1);
v___x_770_ = lean_usize_land(v_x_762_, v___x_769_);
v_j_771_ = lean_usize_to_nat(v___x_770_);
v___x_772_ = lean_array_get_size(v_es_766_);
v___x_773_ = lean_nat_dec_lt(v_j_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_dec(v_j_771_);
lean_dec(v_x_765_);
lean_dec(v_x_764_);
return v_x_761_;
}
else
{
lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_810_; 
lean_inc_ref(v_es_766_);
v_isSharedCheck_810_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v_x_761_, 0);
lean_dec(v_unused_811_);
v___x_775_ = v_x_761_;
v_isShared_776_ = v_isSharedCheck_810_;
goto v_resetjp_774_;
}
else
{
lean_dec(v_x_761_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_810_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_v_777_; lean_object* v___x_778_; lean_object* v_xs_x27_779_; lean_object* v___y_781_; 
v_v_777_ = lean_array_fget(v_es_766_, v_j_771_);
v___x_778_ = lean_box(0);
v_xs_x27_779_ = lean_array_fset(v_es_766_, v_j_771_, v___x_778_);
switch(lean_obj_tag(v_v_777_))
{
case 0:
{
lean_object* v_key_786_; lean_object* v_val_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_797_; 
v_key_786_ = lean_ctor_get(v_v_777_, 0);
v_val_787_ = lean_ctor_get(v_v_777_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_v_777_);
if (v_isSharedCheck_797_ == 0)
{
v___x_789_ = v_v_777_;
v_isShared_790_ = v_isSharedCheck_797_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_val_787_);
lean_inc(v_key_786_);
lean_dec(v_v_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_797_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
uint8_t v___x_791_; 
v___x_791_ = l_Lean_instBEqFVarId_beq(v_x_764_, v_key_786_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_del_object(v___x_789_);
v___x_792_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_786_, v_val_787_, v_x_764_, v_x_765_);
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
v___y_781_ = v___x_793_;
goto v___jp_780_;
}
else
{
lean_object* v___x_795_; 
lean_dec(v_val_787_);
lean_dec(v_key_786_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 1, v_x_765_);
lean_ctor_set(v___x_789_, 0, v_x_764_);
v___x_795_ = v___x_789_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_x_764_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_x_765_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
v___y_781_ = v___x_795_;
goto v___jp_780_;
}
}
}
}
case 1:
{
lean_object* v_node_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_808_; 
v_node_798_ = lean_ctor_get(v_v_777_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v_v_777_);
if (v_isSharedCheck_808_ == 0)
{
v___x_800_ = v_v_777_;
v_isShared_801_ = v_isSharedCheck_808_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_node_798_);
lean_dec(v_v_777_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_808_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_802_ = lean_usize_shift_right(v_x_762_, v___x_767_);
v___x_803_ = lean_usize_add(v_x_763_, v___x_768_);
v___x_804_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_node_798_, v___x_802_, v___x_803_, v_x_764_, v_x_765_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_804_);
v___x_806_ = v___x_800_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v___y_781_ = v___x_806_;
goto v___jp_780_;
}
}
}
default: 
{
lean_object* v___x_809_; 
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v_x_764_);
lean_ctor_set(v___x_809_, 1, v_x_765_);
v___y_781_ = v___x_809_;
goto v___jp_780_;
}
}
v___jp_780_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_array_fset(v_xs_x27_779_, v_j_771_, v___y_781_);
lean_dec(v_j_771_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_782_);
v___x_784_ = v___x_775_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
else
{
lean_object* v_ks_812_; lean_object* v_vs_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_833_; 
v_ks_812_ = lean_ctor_get(v_x_761_, 0);
v_vs_813_ = lean_ctor_get(v_x_761_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_833_ == 0)
{
v___x_815_ = v_x_761_;
v_isShared_816_ = v_isSharedCheck_833_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_vs_813_);
lean_inc(v_ks_812_);
lean_dec(v_x_761_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_833_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_ks_812_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_vs_813_);
v___x_818_ = v_reuseFailAlloc_832_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v_newNode_819_; uint8_t v___y_821_; size_t v___x_827_; uint8_t v___x_828_; 
v_newNode_819_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(v___x_818_, v_x_764_, v_x_765_);
v___x_827_ = ((size_t)7ULL);
v___x_828_ = lean_usize_dec_le(v___x_827_, v_x_763_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_829_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_819_);
v___x_830_ = lean_unsigned_to_nat(4u);
v___x_831_ = lean_nat_dec_lt(v___x_829_, v___x_830_);
lean_dec(v___x_829_);
v___y_821_ = v___x_831_;
goto v___jp_820_;
}
else
{
v___y_821_ = v___x_828_;
goto v___jp_820_;
}
v___jp_820_:
{
if (v___y_821_ == 0)
{
lean_object* v_ks_822_; lean_object* v_vs_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_ks_822_ = lean_ctor_get(v_newNode_819_, 0);
lean_inc_ref(v_ks_822_);
v_vs_823_ = lean_ctor_get(v_newNode_819_, 1);
lean_inc_ref(v_vs_823_);
lean_dec_ref(v_newNode_819_);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__2);
v___x_826_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_x_763_, v_ks_822_, v_vs_823_, v___x_824_, v___x_825_);
lean_dec_ref(v_vs_823_);
lean_dec_ref(v_ks_822_);
return v___x_826_;
}
else
{
return v_newNode_819_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(size_t v_depth_834_, lean_object* v_keys_835_, lean_object* v_vals_836_, lean_object* v_i_837_, lean_object* v_entries_838_){
_start:
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = lean_array_get_size(v_keys_835_);
v___x_840_ = lean_nat_dec_lt(v_i_837_, v___x_839_);
if (v___x_840_ == 0)
{
lean_dec(v_i_837_);
return v_entries_838_;
}
else
{
lean_object* v_k_841_; lean_object* v_v_842_; uint64_t v___x_843_; size_t v_h_844_; size_t v___x_845_; lean_object* v___x_846_; size_t v___x_847_; size_t v___x_848_; size_t v___x_849_; size_t v_h_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_k_841_ = lean_array_fget_borrowed(v_keys_835_, v_i_837_);
v_v_842_ = lean_array_fget_borrowed(v_vals_836_, v_i_837_);
v___x_843_ = l_Lean_instHashableFVarId_hash(v_k_841_);
v_h_844_ = lean_uint64_to_usize(v___x_843_);
v___x_845_ = ((size_t)5ULL);
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = ((size_t)1ULL);
v___x_848_ = lean_usize_sub(v_depth_834_, v___x_847_);
v___x_849_ = lean_usize_mul(v___x_845_, v___x_848_);
v_h_850_ = lean_usize_shift_right(v_h_844_, v___x_849_);
v___x_851_ = lean_nat_add(v_i_837_, v___x_846_);
lean_dec(v_i_837_);
lean_inc(v_v_842_);
lean_inc(v_k_841_);
v___x_852_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_entries_838_, v_h_850_, v_depth_834_, v_k_841_, v_v_842_);
v_i_837_ = v___x_851_;
v_entries_838_ = v___x_852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg___boxed(lean_object* v_depth_854_, lean_object* v_keys_855_, lean_object* v_vals_856_, lean_object* v_i_857_, lean_object* v_entries_858_){
_start:
{
size_t v_depth_boxed_859_; lean_object* v_res_860_; 
v_depth_boxed_859_ = lean_unbox_usize(v_depth_854_);
lean_dec(v_depth_854_);
v_res_860_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_depth_boxed_859_, v_keys_855_, v_vals_856_, v_i_857_, v_entries_858_);
lean_dec_ref(v_vals_856_);
lean_dec_ref(v_keys_855_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___boxed(lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
size_t v_x_29719__boxed_866_; size_t v_x_29720__boxed_867_; lean_object* v_res_868_; 
v_x_29719__boxed_866_ = lean_unbox_usize(v_x_862_);
lean_dec(v_x_862_);
v_x_29720__boxed_867_ = lean_unbox_usize(v_x_863_);
lean_dec(v_x_863_);
v_res_868_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_861_, v_x_29719__boxed_866_, v_x_29720__boxed_867_, v_x_864_, v_x_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
uint64_t v___x_872_; size_t v___x_873_; size_t v___x_874_; lean_object* v___x_875_; 
v___x_872_ = l_Lean_instHashableFVarId_hash(v_x_870_);
v___x_873_ = lean_uint64_to_usize(v___x_872_);
v___x_874_ = ((size_t)1ULL);
v___x_875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_869_, v___x_873_, v___x_874_, v_x_870_, v_x_871_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(lean_object* v_a_876_, lean_object* v_x_877_){
_start:
{
if (lean_obj_tag(v_x_877_) == 0)
{
lean_object* v___x_878_; 
v___x_878_ = lean_box(0);
return v___x_878_;
}
else
{
lean_object* v_key_879_; lean_object* v_value_880_; lean_object* v_tail_881_; uint8_t v___x_882_; 
v_key_879_ = lean_ctor_get(v_x_877_, 0);
v_value_880_ = lean_ctor_get(v_x_877_, 1);
v_tail_881_ = lean_ctor_get(v_x_877_, 2);
v___x_882_ = l_Lean_ExprStructEq_beq(v_key_879_, v_a_876_);
if (v___x_882_ == 0)
{
v_x_877_ = v_tail_881_;
goto _start;
}
else
{
lean_object* v___x_884_; 
lean_inc(v_value_880_);
v___x_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_884_, 0, v_value_880_);
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg___boxed(lean_object* v_a_885_, lean_object* v_x_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_885_, v_x_886_);
lean_dec(v_x_886_);
lean_dec_ref(v_a_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(lean_object* v_m_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_buckets_890_; lean_object* v___x_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v_fold_895_; uint64_t v___x_896_; uint64_t v___x_897_; uint64_t v___x_898_; size_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_buckets_890_ = lean_ctor_get(v_m_888_, 1);
v___x_891_ = lean_array_get_size(v_buckets_890_);
v___x_892_ = l_Lean_ExprStructEq_hash(v_a_889_);
v___x_893_ = 32ULL;
v___x_894_ = lean_uint64_shift_right(v___x_892_, v___x_893_);
v_fold_895_ = lean_uint64_xor(v___x_892_, v___x_894_);
v___x_896_ = 16ULL;
v___x_897_ = lean_uint64_shift_right(v_fold_895_, v___x_896_);
v___x_898_ = lean_uint64_xor(v_fold_895_, v___x_897_);
v___x_899_ = lean_uint64_to_usize(v___x_898_);
v___x_900_ = lean_usize_of_nat(v___x_891_);
v___x_901_ = ((size_t)1ULL);
v___x_902_ = lean_usize_sub(v___x_900_, v___x_901_);
v___x_903_ = lean_usize_land(v___x_899_, v___x_902_);
v___x_904_ = lean_array_uget_borrowed(v_buckets_890_, v___x_903_);
v___x_905_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_889_, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg___boxed(lean_object* v_m_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_906_, v_a_907_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_m_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(lean_object* v_x_909_, uint8_t v_isExporting_910_, uint8_t v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; lean_object* v_env_919_; uint8_t v_isExporting_920_; lean_object* v___x_921_; lean_object* v_env_922_; lean_object* v_nextMacroScope_923_; lean_object* v_ngen_924_; lean_object* v_auxDeclNGen_925_; lean_object* v_traceState_926_; lean_object* v_messages_927_; lean_object* v_infoState_928_; lean_object* v_snapshotTasks_929_; lean_object* v_newDecls_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_985_; 
v___x_918_ = lean_st_ref_get(v___y_916_);
v_env_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc_ref(v_env_919_);
lean_dec(v___x_918_);
v_isExporting_920_ = lean_ctor_get_uint8(v_env_919_, sizeof(void*)*8);
lean_dec_ref(v_env_919_);
v___x_921_ = lean_st_ref_take(v___y_916_);
v_env_922_ = lean_ctor_get(v___x_921_, 0);
v_nextMacroScope_923_ = lean_ctor_get(v___x_921_, 1);
v_ngen_924_ = lean_ctor_get(v___x_921_, 2);
v_auxDeclNGen_925_ = lean_ctor_get(v___x_921_, 3);
v_traceState_926_ = lean_ctor_get(v___x_921_, 4);
v_messages_927_ = lean_ctor_get(v___x_921_, 6);
v_infoState_928_ = lean_ctor_get(v___x_921_, 7);
v_snapshotTasks_929_ = lean_ctor_get(v___x_921_, 8);
v_newDecls_930_ = lean_ctor_get(v___x_921_, 9);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; 
v_unused_986_ = lean_ctor_get(v___x_921_, 5);
lean_dec(v_unused_986_);
v___x_932_ = v___x_921_;
v_isShared_933_ = v_isSharedCheck_985_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_newDecls_930_);
lean_inc(v_snapshotTasks_929_);
lean_inc(v_infoState_928_);
lean_inc(v_messages_927_);
lean_inc(v_traceState_926_);
lean_inc(v_auxDeclNGen_925_);
lean_inc(v_ngen_924_);
lean_inc(v_nextMacroScope_923_);
lean_inc(v_env_922_);
lean_dec(v___x_921_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_985_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_934_ = l_Lean_Environment_setExporting(v_env_922_, v_isExporting_910_);
v___x_935_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 5, v___x_935_);
lean_ctor_set(v___x_932_, 0, v___x_934_);
v___x_937_ = v___x_932_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_nextMacroScope_923_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_ngen_924_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_auxDeclNGen_925_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v_traceState_926_);
lean_ctor_set(v_reuseFailAlloc_984_, 5, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_984_, 6, v_messages_927_);
lean_ctor_set(v_reuseFailAlloc_984_, 7, v_infoState_928_);
lean_ctor_set(v_reuseFailAlloc_984_, 8, v_snapshotTasks_929_);
lean_ctor_set(v_reuseFailAlloc_984_, 9, v_newDecls_930_);
v___x_937_ = v_reuseFailAlloc_984_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_mctx_940_; lean_object* v_zetaDeltaFVarIds_941_; lean_object* v_postponed_942_; lean_object* v_diag_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_982_; 
v___x_938_ = lean_st_ref_set(v___y_916_, v___x_937_);
v___x_939_ = lean_st_ref_take(v___y_914_);
v_mctx_940_ = lean_ctor_get(v___x_939_, 0);
v_zetaDeltaFVarIds_941_ = lean_ctor_get(v___x_939_, 2);
v_postponed_942_ = lean_ctor_get(v___x_939_, 3);
v_diag_943_ = lean_ctor_get(v___x_939_, 4);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v___x_939_, 1);
lean_dec(v_unused_983_);
v___x_945_ = v___x_939_;
v_isShared_946_ = v_isSharedCheck_982_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_diag_943_);
lean_inc(v_postponed_942_);
lean_inc(v_zetaDeltaFVarIds_941_);
lean_inc(v_mctx_940_);
lean_dec(v___x_939_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_982_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_mctx_940_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_zetaDeltaFVarIds_941_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_postponed_942_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_diag_943_);
v___x_949_ = v_reuseFailAlloc_981_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_r_952_; 
v___x_950_ = lean_st_ref_set(v___y_914_, v___x_949_);
v___x_951_ = lean_box(v___y_911_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
v_r_952_ = lean_apply_7(v_x_909_, v___x_951_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, lean_box(0));
if (lean_obj_tag(v_r_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_969_; 
v_a_953_ = lean_ctor_get(v_r_952_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v_r_952_);
if (v_isSharedCheck_969_ == 0)
{
v___x_955_ = v_r_952_;
v_isShared_956_ = v_isSharedCheck_969_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v_r_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_969_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
lean_inc(v_a_953_);
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 1);
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_968_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v___x_959_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_916_, v_isExporting_920_, v___x_935_, v___y_914_, v___x_947_, v___x_958_);
lean_dec_ref(v___x_958_);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v___x_959_, 0);
lean_dec(v_unused_967_);
v___x_961_ = v___x_959_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_dec(v___x_959_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v_a_953_);
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_953_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
v_a_970_ = lean_ctor_get(v_r_952_, 0);
lean_inc(v_a_970_);
lean_dec_ref(v_r_952_);
v___x_971_ = lean_box(0);
v___x_972_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_916_, v_isExporting_920_, v___x_935_, v___y_914_, v___x_947_, v___x_971_);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; 
v_unused_980_ = lean_ctor_get(v___x_972_, 0);
lean_dec(v_unused_980_);
v___x_974_ = v___x_972_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_dec(v___x_972_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set_tag(v___x_974_, 1);
lean_ctor_set(v___x_974_, 0, v_a_970_);
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_970_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg___boxed(lean_object* v_x_987_, lean_object* v_isExporting_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
uint8_t v_isExporting_boxed_996_; uint8_t v___y_29955__boxed_997_; lean_object* v_res_998_; 
v_isExporting_boxed_996_ = lean_unbox(v_isExporting_988_);
v___y_29955__boxed_997_ = lean_unbox(v___y_989_);
v_res_998_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_987_, v_isExporting_boxed_996_, v___y_29955__boxed_997_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(lean_object* v_x_999_, uint8_t v_when_1000_, uint8_t v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
if (v_when_1000_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_box(v___y_1001_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
lean_inc(v___y_1002_);
v___x_1009_ = lean_apply_7(v_x_999_, v___x_1008_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, lean_box(0));
return v___x_1009_;
}
else
{
uint8_t v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = 0;
v___x_1011_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_999_, v___x_1010_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___boxed(lean_object* v_x_1012_, lean_object* v_when_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
uint8_t v_when_boxed_1021_; uint8_t v___y_30088__boxed_1022_; lean_object* v_res_1023_; 
v_when_boxed_1021_ = lean_unbox(v_when_1013_);
v___y_30088__boxed_1022_ = lean_unbox(v___y_1014_);
v_res_1023_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_1012_, v_when_boxed_1021_, v___y_30088__boxed_1022_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0(lean_object* v_proof_1024_, uint8_t v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
v___x_1032_ = lean_infer_type(v_proof_1024_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0___boxed(lean_object* v_proof_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
uint8_t v___y_30117__boxed_1041_; lean_object* v_res_1042_; 
v___y_30117__boxed_1041_ = lean_unbox(v___y_1034_);
v_res_1042_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0(v_proof_1033_, v___y_30117__boxed_1041_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object* v_proof_1043_, uint8_t v_cache_1044_, lean_object* v_postprocessType_1045_, uint8_t v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___f_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; 
lean_inc_ref(v_proof_1043_);
v___f_1053_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1053_, 0, v_proof_1043_);
v___x_1054_ = 1;
v___x_1055_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v___f_1053_, v___x_1054_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1057_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref(v___x_1055_);
v___x_1057_ = l_Lean_Core_betaReduce(v_a_1056_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1059_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = l_Lean_Meta_zetaReduce(v_a_1058_, v___x_1054_, v___x_1054_, v___x_1054_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref(v___x_1059_);
v___x_1061_ = lean_box(v___y_1046_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
lean_inc(v___y_1047_);
v___x_1062_ = lean_apply_8(v_postprocessType_1045_, v_a_1060_, v___x_1061_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, lean_box(0));
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; uint8_t v___y_1065_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref(v___x_1062_);
if (v_cache_1044_ == 0)
{
v___y_1065_ = v_cache_1044_;
goto v___jp_1064_;
}
else
{
uint8_t v___x_1068_; 
v___x_1068_ = l_Lean_Expr_hasSorry(v_proof_1043_);
if (v___x_1068_ == 0)
{
v___y_1065_ = v_cache_1044_;
goto v___jp_1064_;
}
else
{
uint8_t v___x_1069_; 
v___x_1069_ = 0;
v___y_1065_ = v___x_1069_;
goto v___jp_1064_;
}
}
v___jp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = l_Lean_Meta_mkAuxTheorem(v_a_1063_, v_proof_1043_, v___x_1054_, v___x_1066_, v___y_1065_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
return v___x_1067_;
}
}
else
{
lean_dec_ref(v_proof_1043_);
return v___x_1062_;
}
}
else
{
lean_dec_ref(v_postprocessType_1045_);
lean_dec_ref(v_proof_1043_);
return v___x_1059_;
}
}
else
{
lean_dec_ref(v_postprocessType_1045_);
lean_dec_ref(v_proof_1043_);
return v___x_1057_;
}
}
else
{
lean_dec_ref(v_postprocessType_1045_);
lean_dec_ref(v_proof_1043_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object* v_proof_1070_, lean_object* v_cache_1071_, lean_object* v_postprocessType_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
uint8_t v_cache_boxed_1080_; uint8_t v___y_30140__boxed_1081_; lean_object* v_res_1082_; 
v_cache_boxed_1080_ = lean_unbox(v_cache_1071_);
v___y_30140__boxed_1081_ = lean_unbox(v___y_1073_);
v_res_1082_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_proof_1070_, v_cache_boxed_1080_, v_postprocessType_1072_, v___y_30140__boxed_1081_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
if (lean_obj_tag(v_x_1084_) == 0)
{
return v_x_1083_;
}
else
{
lean_object* v_key_1085_; lean_object* v_value_1086_; lean_object* v_tail_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1110_; 
v_key_1085_ = lean_ctor_get(v_x_1084_, 0);
v_value_1086_ = lean_ctor_get(v_x_1084_, 1);
v_tail_1087_ = lean_ctor_get(v_x_1084_, 2);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_x_1084_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1089_ = v_x_1084_;
v_isShared_1090_ = v_isSharedCheck_1110_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_tail_1087_);
lean_inc(v_value_1086_);
lean_inc(v_key_1085_);
lean_dec(v_x_1084_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1110_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; uint64_t v___x_1092_; uint64_t v___x_1093_; uint64_t v___x_1094_; uint64_t v_fold_1095_; uint64_t v___x_1096_; uint64_t v___x_1097_; uint64_t v___x_1098_; size_t v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1091_ = lean_array_get_size(v_x_1083_);
v___x_1092_ = l_Lean_ExprStructEq_hash(v_key_1085_);
v___x_1093_ = 32ULL;
v___x_1094_ = lean_uint64_shift_right(v___x_1092_, v___x_1093_);
v_fold_1095_ = lean_uint64_xor(v___x_1092_, v___x_1094_);
v___x_1096_ = 16ULL;
v___x_1097_ = lean_uint64_shift_right(v_fold_1095_, v___x_1096_);
v___x_1098_ = lean_uint64_xor(v_fold_1095_, v___x_1097_);
v___x_1099_ = lean_uint64_to_usize(v___x_1098_);
v___x_1100_ = lean_usize_of_nat(v___x_1091_);
v___x_1101_ = ((size_t)1ULL);
v___x_1102_ = lean_usize_sub(v___x_1100_, v___x_1101_);
v___x_1103_ = lean_usize_land(v___x_1099_, v___x_1102_);
v___x_1104_ = lean_array_uget_borrowed(v_x_1083_, v___x_1103_);
lean_inc(v___x_1104_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 2, v___x_1104_);
v___x_1106_ = v___x_1089_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_key_1085_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_value_1086_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_array_uset(v_x_1083_, v___x_1103_, v___x_1106_);
v_x_1083_ = v___x_1107_;
v_x_1084_ = v_tail_1087_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(lean_object* v_i_1111_, lean_object* v_source_1112_, lean_object* v_target_1113_){
_start:
{
lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = lean_array_get_size(v_source_1112_);
v___x_1115_ = lean_nat_dec_lt(v_i_1111_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_dec_ref(v_source_1112_);
lean_dec(v_i_1111_);
return v_target_1113_;
}
else
{
lean_object* v_es_1116_; lean_object* v___x_1117_; lean_object* v_source_1118_; lean_object* v_target_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_es_1116_ = lean_array_fget(v_source_1112_, v_i_1111_);
v___x_1117_ = lean_box(0);
v_source_1118_ = lean_array_fset(v_source_1112_, v_i_1111_, v___x_1117_);
v_target_1119_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(v_target_1113_, v_es_1116_);
v___x_1120_ = lean_unsigned_to_nat(1u);
v___x_1121_ = lean_nat_add(v_i_1111_, v___x_1120_);
lean_dec(v_i_1111_);
v_i_1111_ = v___x_1121_;
v_source_1112_ = v_source_1118_;
v_target_1113_ = v_target_1119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(lean_object* v_data_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_nbuckets_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1124_ = lean_array_get_size(v_data_1123_);
v___x_1125_ = lean_unsigned_to_nat(2u);
v_nbuckets_1126_ = lean_nat_mul(v___x_1124_, v___x_1125_);
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_mk_array(v_nbuckets_1126_, v___x_1128_);
v___x_1130_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(v___x_1127_, v_data_1123_, v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object* v_a_1131_, lean_object* v_x_1132_){
_start:
{
if (lean_obj_tag(v_x_1132_) == 0)
{
uint8_t v___x_1133_; 
v___x_1133_ = 0;
return v___x_1133_;
}
else
{
lean_object* v_key_1134_; lean_object* v_tail_1135_; uint8_t v___x_1136_; 
v_key_1134_ = lean_ctor_get(v_x_1132_, 0);
v_tail_1135_ = lean_ctor_get(v_x_1132_, 2);
v___x_1136_ = l_Lean_ExprStructEq_beq(v_key_1134_, v_a_1131_);
if (v___x_1136_ == 0)
{
v_x_1132_ = v_tail_1135_;
goto _start;
}
else
{
return v___x_1136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_1138_, lean_object* v_x_1139_){
_start:
{
uint8_t v_res_1140_; lean_object* v_r_1141_; 
v_res_1140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1138_, v_x_1139_);
lean_dec(v_x_1139_);
lean_dec_ref(v_a_1138_);
v_r_1141_ = lean_box(v_res_1140_);
return v_r_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(lean_object* v_a_1142_, lean_object* v_b_1143_, lean_object* v_x_1144_){
_start:
{
if (lean_obj_tag(v_x_1144_) == 0)
{
lean_dec(v_b_1143_);
lean_dec_ref(v_a_1142_);
return v_x_1144_;
}
else
{
lean_object* v_key_1145_; lean_object* v_value_1146_; lean_object* v_tail_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1159_; 
v_key_1145_ = lean_ctor_get(v_x_1144_, 0);
v_value_1146_ = lean_ctor_get(v_x_1144_, 1);
v_tail_1147_ = lean_ctor_get(v_x_1144_, 2);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1149_ = v_x_1144_;
v_isShared_1150_ = v_isSharedCheck_1159_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_tail_1147_);
lean_inc(v_value_1146_);
lean_inc(v_key_1145_);
lean_dec(v_x_1144_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1159_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
uint8_t v___x_1151_; 
v___x_1151_ = l_Lean_ExprStructEq_beq(v_key_1145_, v_a_1142_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1142_, v_b_1143_, v_tail_1147_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 2, v___x_1152_);
v___x_1154_ = v___x_1149_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_key_1145_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_value_1146_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_value_1146_);
lean_dec(v_key_1145_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v_b_1143_);
lean_ctor_set(v___x_1149_, 0, v_a_1142_);
v___x_1157_ = v___x_1149_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1142_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_b_1143_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_tail_1147_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object* v_m_1160_, lean_object* v_a_1161_, lean_object* v_b_1162_){
_start:
{
lean_object* v_size_1163_; lean_object* v_buckets_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1207_; 
v_size_1163_ = lean_ctor_get(v_m_1160_, 0);
v_buckets_1164_ = lean_ctor_get(v_m_1160_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_m_1160_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1166_ = v_m_1160_;
v_isShared_1167_ = v_isSharedCheck_1207_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_buckets_1164_);
lean_inc(v_size_1163_);
lean_dec(v_m_1160_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1207_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; uint64_t v___x_1169_; uint64_t v___x_1170_; uint64_t v___x_1171_; uint64_t v_fold_1172_; uint64_t v___x_1173_; uint64_t v___x_1174_; uint64_t v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; lean_object* v_bkt_1181_; uint8_t v___x_1182_; 
v___x_1168_ = lean_array_get_size(v_buckets_1164_);
v___x_1169_ = l_Lean_ExprStructEq_hash(v_a_1161_);
v___x_1170_ = 32ULL;
v___x_1171_ = lean_uint64_shift_right(v___x_1169_, v___x_1170_);
v_fold_1172_ = lean_uint64_xor(v___x_1169_, v___x_1171_);
v___x_1173_ = 16ULL;
v___x_1174_ = lean_uint64_shift_right(v_fold_1172_, v___x_1173_);
v___x_1175_ = lean_uint64_xor(v_fold_1172_, v___x_1174_);
v___x_1176_ = lean_uint64_to_usize(v___x_1175_);
v___x_1177_ = lean_usize_of_nat(v___x_1168_);
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_sub(v___x_1177_, v___x_1178_);
v___x_1180_ = lean_usize_land(v___x_1176_, v___x_1179_);
v_bkt_1181_ = lean_array_uget_borrowed(v_buckets_1164_, v___x_1180_);
v___x_1182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1161_, v_bkt_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v_size_x27_1184_; lean_object* v___x_1185_; lean_object* v_buckets_x27_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1183_ = lean_unsigned_to_nat(1u);
v_size_x27_1184_ = lean_nat_add(v_size_1163_, v___x_1183_);
lean_dec(v_size_1163_);
lean_inc(v_bkt_1181_);
v___x_1185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1185_, 0, v_a_1161_);
lean_ctor_set(v___x_1185_, 1, v_b_1162_);
lean_ctor_set(v___x_1185_, 2, v_bkt_1181_);
v_buckets_x27_1186_ = lean_array_uset(v_buckets_1164_, v___x_1180_, v___x_1185_);
v___x_1187_ = lean_unsigned_to_nat(4u);
v___x_1188_ = lean_nat_mul(v_size_x27_1184_, v___x_1187_);
v___x_1189_ = lean_unsigned_to_nat(3u);
v___x_1190_ = lean_nat_div(v___x_1188_, v___x_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_array_get_size(v_buckets_x27_1186_);
v___x_1192_ = lean_nat_dec_le(v___x_1190_, v___x_1191_);
lean_dec(v___x_1190_);
if (v___x_1192_ == 0)
{
lean_object* v_val_1193_; lean_object* v___x_1195_; 
v_val_1193_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(v_buckets_x27_1186_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v_val_1193_);
lean_ctor_set(v___x_1166_, 0, v_size_x27_1184_);
v___x_1195_ = v___x_1166_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_size_x27_1184_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_val_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
else
{
lean_object* v___x_1198_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v_buckets_x27_1186_);
lean_ctor_set(v___x_1166_, 0, v_size_x27_1184_);
v___x_1198_ = v___x_1166_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_size_x27_1184_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_buckets_x27_1186_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_object* v___x_1200_; lean_object* v_buckets_x27_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
lean_inc(v_bkt_1181_);
v___x_1200_ = lean_box(0);
v_buckets_x27_1201_ = lean_array_uset(v_buckets_1164_, v___x_1180_, v___x_1200_);
v___x_1202_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1161_, v_b_1162_, v_bkt_1181_);
v___x_1203_ = lean_array_uset(v_buckets_x27_1201_, v___x_1180_, v___x_1202_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v___x_1203_);
v___x_1205_ = v___x_1166_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_size_1163_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object* v_e_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
uint8_t v_a_boxed_1217_; lean_object* v_res_1218_; 
v_a_boxed_1217_ = lean_unbox(v_a_1210_);
v_res_1218_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1209_, v_a_boxed_1217_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object* v_as_1219_, size_t v_sz_1220_, size_t v_i_1221_, lean_object* v_b_1222_, uint8_t v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_a_1231_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; uint8_t v___x_1244_; 
v___x_1244_ = lean_usize_dec_lt(v_i_1221_, v_sz_1220_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_b_1222_);
return v___x_1245_;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1247_; lean_object* v_localDecl_1249_; lean_object* v___x_1257_; 
v_a_1246_ = lean_array_uget_borrowed(v_as_1219_, v_i_1221_);
v___x_1247_ = l_Lean_Expr_fvarId_x21(v_a_1246_);
lean_inc(v___x_1247_);
v___x_1257_ = l_Lean_FVarId_getDecl___redArg(v___x_1247_, v___y_1225_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref(v___x_1257_);
v___x_1259_ = l_Lean_LocalDecl_type(v_a_1258_);
v___x_1260_ = l_Lean_Meta_AbstractNestedProofs_visit(v___x_1259_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref(v___x_1260_);
v___x_1262_ = l_Lean_LocalDecl_setType(v_a_1258_, v_a_1261_);
v___x_1263_ = l_Lean_LocalDecl_value_x3f(v___x_1262_, v___x_1244_);
if (lean_obj_tag(v___x_1263_) == 0)
{
v_localDecl_1249_ = v___x_1262_;
goto v___jp_1248_;
}
else
{
lean_object* v_val_1264_; lean_object* v___x_1265_; 
v_val_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_val_1264_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = l_Lean_Meta_AbstractNestedProofs_visit(v_val_1264_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1267_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref(v___x_1265_);
v___x_1267_ = l_Lean_LocalDecl_setValue(v___x_1262_, v_a_1266_);
v_localDecl_1249_ = v___x_1267_;
goto v___jp_1248_;
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v___x_1262_);
lean_dec(v___x_1247_);
lean_dec_ref(v_b_1222_);
v_a_1268_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1265_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1265_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v_a_1258_);
lean_dec(v___x_1247_);
lean_dec_ref(v_b_1222_);
v_a_1276_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1260_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1260_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v___x_1247_);
lean_dec_ref(v_b_1222_);
v_a_1284_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1257_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1257_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
v___jp_1248_:
{
lean_object* v_fvarIdToDecl_1250_; lean_object* v_decls_1251_; lean_object* v_auxDeclToFullName_1252_; lean_object* v___x_1253_; 
v_fvarIdToDecl_1250_ = lean_ctor_get(v_b_1222_, 0);
v_decls_1251_ = lean_ctor_get(v_b_1222_, 1);
v_auxDeclToFullName_1252_ = lean_ctor_get(v_b_1222_, 2);
lean_inc_ref(v_b_1222_);
v___x_1253_ = lean_local_ctx_find(v_b_1222_, v___x_1247_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_dec_ref(v_localDecl_1249_);
v_a_1231_ = v_b_1222_;
goto v___jp_1230_;
}
else
{
lean_object* v_index_1254_; lean_object* v_fvarId_1255_; lean_object* v___x_1256_; 
lean_inc(v_auxDeclToFullName_1252_);
lean_inc_ref(v_decls_1251_);
lean_inc_ref(v_fvarIdToDecl_1250_);
lean_dec_ref(v___x_1253_);
lean_dec_ref(v_b_1222_);
v_index_1254_ = lean_ctor_get(v_localDecl_1249_, 0);
lean_inc(v_index_1254_);
v_fvarId_1255_ = lean_ctor_get(v_localDecl_1249_, 1);
lean_inc_ref(v_localDecl_1249_);
lean_inc(v_fvarId_1255_);
v___x_1256_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_fvarIdToDecl_1250_, v_fvarId_1255_, v_localDecl_1249_);
v___y_1236_ = v___x_1256_;
v___y_1237_ = v_decls_1251_;
v___y_1238_ = v_auxDeclToFullName_1252_;
v___y_1239_ = v_localDecl_1249_;
v___y_1240_ = v_index_1254_;
goto v___jp_1235_;
}
}
}
v___jp_1230_:
{
size_t v___x_1232_; size_t v___x_1233_; 
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_add(v_i_1221_, v___x_1232_);
v_i_1221_ = v___x_1233_;
v_b_1222_ = v_a_1231_;
goto _start;
}
v___jp_1235_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___y_1239_);
v___x_1242_ = l_Lean_PersistentArray_set___redArg(v___y_1237_, v___y_1240_, v___x_1241_);
lean_dec(v___y_1240_);
v___x_1243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1243_, 0, v___y_1236_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
lean_ctor_set(v___x_1243_, 2, v___y_1238_);
v_a_1231_ = v___x_1243_;
goto v___jp_1230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object* v_xs_1292_, lean_object* v_k_1293_, uint8_t v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_lctx_1301_; lean_object* v_localInstances_1302_; size_t v_sz_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v_lctx_1301_ = lean_ctor_get(v___y_1296_, 2);
v_localInstances_1302_ = lean_ctor_get(v___y_1296_, 3);
v_sz_1303_ = lean_array_size(v_xs_1292_);
v___x_1304_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1301_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_xs_1292_, v_sz_1303_, v___x_1304_, v_lctx_1301_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1307_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref(v___x_1305_);
lean_inc_ref(v_localInstances_1302_);
v___x_1307_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_a_1306_, v_localInstances_1302_, v_k_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
return v___x_1307_;
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec_ref(v_k_1293_);
v_a_1308_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1305_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1305_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object* v_xs_1316_, lean_object* v_k_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
uint8_t v___y_30455__boxed_1325_; lean_object* v_res_1326_; 
v___y_30455__boxed_1325_ = lean_unbox(v___y_1318_);
v_res_1326_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(v_xs_1316_, v_k_1317_, v___y_30455__boxed_1325_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v_xs_1316_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object* v___y_1327_, lean_object* v___f_1328_, lean_object* v_xs_1329_, lean_object* v_b_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
uint8_t v___y_30405__boxed_1338_; uint8_t v___y_30407__boxed_1339_; lean_object* v_res_1340_; 
v___y_30405__boxed_1338_ = lean_unbox(v___y_1327_);
v___y_30407__boxed_1339_ = lean_unbox(v___y_1331_);
v_res_1340_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(v___y_30405__boxed_1338_, v___f_1328_, v_xs_1329_, v_b_1330_, v___y_30407__boxed_1339_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object* v_b_1341_, lean_object* v_xs_1342_, uint8_t v___y_1343_, uint8_t v___x_1344_, uint8_t v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1341_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = 1;
v___x_1355_ = l_Lean_Meta_mkForallFVars(v_xs_1342_, v_a_1353_, v___y_1343_, v___x_1344_, v___x_1344_, v___x_1354_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1355_;
}
else
{
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object* v_b_1356_, lean_object* v_xs_1357_, lean_object* v___y_1358_, lean_object* v___x_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
uint8_t v___y_30441__boxed_1367_; uint8_t v___x_30442__boxed_1368_; uint8_t v___y_30443__boxed_1369_; lean_object* v_res_1370_; 
v___y_30441__boxed_1367_ = lean_unbox(v___y_1358_);
v___x_30442__boxed_1368_ = lean_unbox(v___x_1359_);
v___y_30443__boxed_1369_ = lean_unbox(v___y_1360_);
v_res_1370_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(v_b_1356_, v_xs_1357_, v___y_30441__boxed_1367_, v___x_30442__boxed_1368_, v___y_30443__boxed_1369_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v_xs_1357_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t v___y_1371_, uint8_t v___x_1372_, lean_object* v___f_1373_, lean_object* v_xs_1374_, lean_object* v_b_1375_, uint8_t v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___f_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1383_ = lean_box(v___y_1371_);
v___x_1384_ = lean_box(v___x_1372_);
lean_inc_ref(v_xs_1374_);
v___f_1385_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1385_, 0, v_b_1375_);
lean_closure_set(v___f_1385_, 1, v_xs_1374_);
lean_closure_set(v___f_1385_, 2, v___x_1383_);
lean_closure_set(v___f_1385_, 3, v___x_1384_);
v___x_1386_ = lean_box(v___y_1376_);
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
lean_inc(v___y_1379_);
lean_inc_ref(v___y_1378_);
lean_inc(v___y_1377_);
v___x_1387_ = lean_apply_9(v___f_1373_, v_xs_1374_, v___f_1385_, v___x_1386_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, lean_box(0));
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object* v___y_1388_, lean_object* v___x_1389_, lean_object* v___f_1390_, lean_object* v_xs_1391_, lean_object* v_b_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
uint8_t v___y_30416__boxed_1400_; uint8_t v___x_30417__boxed_1401_; uint8_t v___y_30419__boxed_1402_; lean_object* v_res_1403_; 
v___y_30416__boxed_1400_ = lean_unbox(v___y_1388_);
v___x_30417__boxed_1401_ = lean_unbox(v___x_1389_);
v___y_30419__boxed_1402_ = lean_unbox(v___y_1393_);
v_res_1403_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(v___y_30416__boxed_1400_, v___x_30417__boxed_1401_, v___f_1390_, v_xs_1391_, v_b_1392_, v___y_30419__boxed_1402_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t v_sz_1404_, size_t v_i_1405_, lean_object* v_bs_1406_, uint8_t v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
uint8_t v___x_1414_; 
v___x_1414_ = lean_usize_dec_lt(v_i_1405_, v_sz_1404_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v_bs_1406_);
return v___x_1415_;
}
else
{
lean_object* v_v_1416_; lean_object* v___x_1417_; 
v_v_1416_ = lean_array_uget_borrowed(v_bs_1406_, v_i_1405_);
lean_inc(v_v_1416_);
v___x_1417_ = l_Lean_Meta_AbstractNestedProofs_visit(v_v_1416_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; lean_object* v_bs_x27_1420_; size_t v___x_1421_; size_t v___x_1422_; lean_object* v___x_1423_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
v___x_1419_ = lean_unsigned_to_nat(0u);
v_bs_x27_1420_ = lean_array_uset(v_bs_1406_, v_i_1405_, v___x_1419_);
v___x_1421_ = ((size_t)1ULL);
v___x_1422_ = lean_usize_add(v_i_1405_, v___x_1421_);
v___x_1423_ = lean_array_uset(v_bs_x27_1420_, v_i_1405_, v_a_1418_);
v_i_1405_ = v___x_1422_;
v_bs_1406_ = v___x_1423_;
goto _start;
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v_bs_1406_);
v_a_1425_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1417_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1417_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_, uint8_t v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
if (lean_obj_tag(v_x_1433_) == 5)
{
lean_object* v_fn_1443_; lean_object* v_arg_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_fn_1443_ = lean_ctor_get(v_x_1433_, 0);
lean_inc_ref(v_fn_1443_);
v_arg_1444_ = lean_ctor_get(v_x_1433_, 1);
lean_inc_ref(v_arg_1444_);
lean_dec_ref(v_x_1433_);
v___x_1445_ = lean_array_set(v_x_1434_, v_x_1435_, v_arg_1444_);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_sub(v_x_1435_, v___x_1446_);
lean_dec(v_x_1435_);
v_x_1433_ = v_fn_1443_;
v_x_1434_ = v___x_1445_;
v_x_1435_ = v___x_1447_;
goto _start;
}
else
{
lean_object* v___x_1449_; 
lean_dec(v_x_1435_);
v___x_1449_ = l_Lean_Meta_AbstractNestedProofs_visit(v_x_1433_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; size_t v_sz_1451_; size_t v___x_1452_; lean_object* v___x_1453_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref(v___x_1449_);
v_sz_1451_ = lean_array_size(v_x_1434_);
v___x_1452_ = ((size_t)0ULL);
v___x_1453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_1451_, v___x_1452_, v_x_1434_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1462_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1462_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1462_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = l_Lean_mkAppN(v_a_1450_, v_a_1454_);
lean_dec(v_a_1454_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1458_);
v___x_1460_ = v___x_1456_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_a_1450_);
v_a_1463_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1453_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1453_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
else
{
lean_dec_ref(v_x_1434_);
return v___x_1449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object* v_e_1471_, uint8_t v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_a_1480_; lean_object* v___y_1486_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_visit___closed__0));
v___x_1489_ = l_Lean_Core_checkSystem(v___x_1488_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1556_; 
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; 
v_unused_1557_ = lean_ctor_get(v___x_1489_, 0);
lean_dec(v_unused_1557_);
v___x_1491_ = v___x_1489_;
v_isShared_1492_ = v_isSharedCheck_1556_;
goto v_resetjp_1490_;
}
else
{
lean_dec(v___x_1489_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1556_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
uint8_t v___x_1493_; 
v___x_1493_ = l_Lean_Expr_isAtomic(v_e_1471_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_st_ref_get(v_a_1473_);
v___x_1495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v___x_1494_, v_e_1471_);
lean_dec(v___x_1494_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v___x_1496_; 
lean_del_object(v___x_1491_);
lean_inc_ref(v_e_1471_);
v___x_1496_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_1471_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___f_1501_; uint8_t v___x_1502_; uint8_t v___y_1504_; uint8_t v___x_1538_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref(v___x_1496_);
v___f_1501_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed), 9, 0);
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
v___x_1540_ = l_Lean_Expr_hasSorry(v_e_1471_);
if (v___x_1540_ == 0)
{
lean_dec_ref(v___f_1501_);
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
lean_dec_ref(v___f_1501_);
goto v___jp_1498_;
}
}
}
v___jp_1498_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___boxed), 8, 0);
lean_inc_ref(v_e_1471_);
v___x_1500_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_e_1471_, v_a_1472_, v___x_1499_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
v___y_1486_ = v___x_1500_;
goto v___jp_1485_;
}
v___jp_1503_:
{
switch(lean_obj_tag(v_e_1471_))
{
case 6:
{
lean_object* v___x_1505_; lean_object* v___f_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_box(v___y_1504_);
v___f_1506_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1506_, 0, v___x_1505_);
lean_closure_set(v___f_1506_, 1, v___f_1501_);
lean_inc_ref(v_e_1471_);
v___x_1507_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1471_, v___f_1506_, v___y_1504_, v___x_1502_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
v___y_1486_ = v___x_1507_;
goto v___jp_1485_;
}
case 8:
{
lean_object* v___x_1508_; lean_object* v___f_1509_; lean_object* v___x_1510_; 
v___x_1508_ = lean_box(v___y_1504_);
v___f_1509_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1509_, 0, v___x_1508_);
lean_closure_set(v___f_1509_, 1, v___f_1501_);
lean_inc_ref(v_e_1471_);
v___x_1510_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1471_, v___f_1509_, v___y_1504_, v___x_1502_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
v___y_1486_ = v___x_1510_;
goto v___jp_1485_;
}
case 7:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___f_1513_; lean_object* v___x_1514_; 
v___x_1511_ = lean_box(v___y_1504_);
v___x_1512_ = lean_box(v___x_1502_);
v___f_1513_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed), 12, 3);
lean_closure_set(v___f_1513_, 0, v___x_1511_);
lean_closure_set(v___f_1513_, 1, v___x_1512_);
lean_closure_set(v___f_1513_, 2, v___f_1501_);
lean_inc_ref(v_e_1471_);
v___x_1514_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_e_1471_, v___f_1513_, v___y_1504_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
v___y_1486_ = v___x_1514_;
goto v___jp_1485_;
}
case 10:
{
lean_object* v_data_1515_; lean_object* v_expr_1516_; lean_object* v___x_1517_; 
lean_dec_ref(v___f_1501_);
v_data_1515_ = lean_ctor_get(v_e_1471_, 0);
v_expr_1516_ = lean_ctor_get(v_e_1471_, 1);
lean_inc_ref(v_expr_1516_);
v___x_1517_ = l_Lean_Meta_AbstractNestedProofs_visit(v_expr_1516_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
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
v_a_1480_ = v___x_1522_;
goto v___jp_1479_;
}
else
{
lean_dec(v_a_1518_);
lean_inc_ref(v_e_1471_);
v_a_1480_ = v_e_1471_;
goto v___jp_1479_;
}
}
else
{
v___y_1486_ = v___x_1517_;
goto v___jp_1485_;
}
}
case 11:
{
lean_object* v_typeName_1523_; lean_object* v_idx_1524_; lean_object* v_struct_1525_; lean_object* v___x_1526_; 
lean_dec_ref(v___f_1501_);
v_typeName_1523_ = lean_ctor_get(v_e_1471_, 0);
v_idx_1524_ = lean_ctor_get(v_e_1471_, 1);
v_struct_1525_ = lean_ctor_get(v_e_1471_, 2);
lean_inc_ref(v_struct_1525_);
v___x_1526_ = l_Lean_Meta_AbstractNestedProofs_visit(v_struct_1525_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
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
v_a_1480_ = v___x_1531_;
goto v___jp_1479_;
}
else
{
lean_dec(v_a_1527_);
lean_inc_ref(v_e_1471_);
v_a_1480_ = v_e_1471_;
goto v___jp_1479_;
}
}
else
{
v___y_1486_ = v___x_1526_;
goto v___jp_1485_;
}
}
case 5:
{
lean_object* v_dummy_1532_; lean_object* v_nargs_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec_ref(v___f_1501_);
v_dummy_1532_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_1533_ = l_Lean_Expr_getAppNumArgs(v_e_1471_);
lean_inc(v_nargs_1533_);
v___x_1534_ = lean_mk_array(v_nargs_1533_, v_dummy_1532_);
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_nat_sub(v_nargs_1533_, v___x_1535_);
lean_dec(v_nargs_1533_);
lean_inc_ref(v_e_1471_);
v___x_1537_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_e_1471_, v___x_1534_, v___x_1536_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
v___y_1486_ = v___x_1537_;
goto v___jp_1485_;
}
default: 
{
lean_dec_ref(v___f_1501_);
lean_inc_ref(v_e_1471_);
v_a_1480_ = v_e_1471_;
goto v___jp_1479_;
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v_e_1471_);
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
lean_object* v_val_1549_; lean_object* v___x_1551_; 
lean_dec_ref(v_e_1471_);
v_val_1549_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_val_1549_);
lean_dec_ref(v___x_1495_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v_val_1549_);
v___x_1551_ = v___x_1491_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_val_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
else
{
lean_object* v___x_1554_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v_e_1471_);
v___x_1554_ = v___x_1491_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_e_1471_);
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
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v_e_1471_);
v_a_1558_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1489_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1489_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
v___jp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1481_ = lean_st_ref_take(v_a_1473_);
lean_inc_ref(v_a_1480_);
v___x_1482_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v___x_1481_, v_e_1471_, v_a_1480_);
v___x_1483_ = lean_st_ref_set(v_a_1473_, v___x_1482_);
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v_a_1480_);
return v___x_1484_;
}
v___jp_1485_:
{
if (lean_obj_tag(v___y_1486_) == 0)
{
lean_object* v_a_1487_; 
v_a_1487_ = lean_ctor_get(v___y_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref(v___y_1486_);
v_a_1480_ = v_a_1487_;
goto v___jp_1479_;
}
else
{
lean_dec_ref(v_e_1471_);
return v___y_1486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object* v_b_1566_, lean_object* v_xs_1567_, uint8_t v___y_1568_, uint8_t v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1566_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref(v___x_1576_);
v___x_1578_ = 1;
v___x_1579_ = l_Lean_Meta_mkLambdaFVars(v_xs_1567_, v_a_1577_, v___y_1568_, v___y_1568_, v___y_1568_, v___y_1568_, v___x_1578_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
return v___x_1579_;
}
else
{
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object* v_b_1580_, lean_object* v_xs_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
uint8_t v___y_30428__boxed_1590_; uint8_t v___y_30429__boxed_1591_; lean_object* v_res_1592_; 
v___y_30428__boxed_1590_ = lean_unbox(v___y_1582_);
v___y_30429__boxed_1591_ = lean_unbox(v___y_1583_);
v_res_1592_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(v_b_1580_, v_xs_1581_, v___y_30428__boxed_1590_, v___y_30429__boxed_1591_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v_xs_1581_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t v___y_1593_, lean_object* v___f_1594_, lean_object* v_xs_1595_, lean_object* v_b_1596_, uint8_t v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; lean_object* v___f_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1604_ = lean_box(v___y_1593_);
lean_inc_ref(v_xs_1595_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1605_, 0, v_b_1596_);
lean_closure_set(v___f_1605_, 1, v_xs_1595_);
lean_closure_set(v___f_1605_, 2, v___x_1604_);
v___x_1606_ = lean_box(v___y_1597_);
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc(v___y_1598_);
v___x_1607_ = lean_apply_9(v___f_1594_, v_xs_1595_, v___f_1605_, v___x_1606_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, lean_box(0));
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object* v_sz_1608_, lean_object* v_i_1609_, lean_object* v_bs_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
size_t v_sz_boxed_1618_; size_t v_i_boxed_1619_; uint8_t v___y_30468__boxed_1620_; lean_object* v_res_1621_; 
v_sz_boxed_1618_ = lean_unbox_usize(v_sz_1608_);
lean_dec(v_sz_1608_);
v_i_boxed_1619_ = lean_unbox_usize(v_i_1609_);
lean_dec(v_i_1609_);
v___y_30468__boxed_1620_ = lean_unbox(v___y_1611_);
v_res_1621_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_boxed_1618_, v_i_boxed_1619_, v_bs_1610_, v___y_30468__boxed_1620_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object* v_x_1622_, lean_object* v_x_1623_, lean_object* v_x_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
uint8_t v___y_30489__boxed_1632_; lean_object* v_res_1633_; 
v___y_30489__boxed_1632_ = lean_unbox(v___y_1625_);
v_res_1633_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_x_1622_, v_x_1623_, v_x_1624_, v___y_30489__boxed_1632_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object* v_as_1634_, lean_object* v_sz_1635_, lean_object* v_i_1636_, lean_object* v_b_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
size_t v_sz_boxed_1645_; size_t v_i_boxed_1646_; uint8_t v___y_30512__boxed_1647_; lean_object* v_res_1648_; 
v_sz_boxed_1645_ = lean_unbox_usize(v_sz_1635_);
lean_dec(v_sz_1635_);
v_i_boxed_1646_ = lean_unbox_usize(v_i_1636_);
lean_dec(v_i_1636_);
v___y_30512__boxed_1647_ = lean_unbox(v___y_1638_);
v_res_1648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_as_1634_, v_sz_boxed_1645_, v_i_boxed_1646_, v_b_1637_, v___y_30512__boxed_1647_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v_as_1634_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object* v_00_u03b2_1649_, lean_object* v_m_1650_, lean_object* v_a_1651_, lean_object* v_b_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_m_1650_, v_a_1651_, v_b_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object* v_00_u03b2_1654_, lean_object* v_m_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_1655_, v_a_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object* v_00_u03b2_1658_, lean_object* v_m_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_00_u03b2_1658_, v_m_1659_, v_a_1660_);
lean_dec_ref(v_a_1660_);
lean_dec_ref(v_m_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object* v_00_u03b2_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_, lean_object* v_x_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_x_1663_, v_x_1664_, v_x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object* v_00_u03b2_1667_, lean_object* v_a_1668_, lean_object* v_x_1669_){
_start:
{
uint8_t v___x_1670_; 
v___x_1670_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1668_, v_x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1671_, lean_object* v_a_1672_, lean_object* v_x_1673_){
_start:
{
uint8_t v_res_1674_; lean_object* v_r_1675_; 
v_res_1674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(v_00_u03b2_1671_, v_a_1672_, v_x_1673_);
lean_dec(v_x_1673_);
lean_dec_ref(v_a_1672_);
v_r_1675_ = lean_box(v_res_1674_);
return v_r_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2(lean_object* v_00_u03b2_1676_, lean_object* v_data_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(v_data_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3(lean_object* v_00_u03b2_1679_, lean_object* v_a_1680_, lean_object* v_b_1681_, lean_object* v_x_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1680_, v_b_1681_, v_x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(lean_object* v_00_u03b2_1684_, lean_object* v_a_1685_, lean_object* v_x_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_1685_, v_x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1688_, lean_object* v_a_1689_, lean_object* v_x_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(v_00_u03b2_1688_, v_a_1689_, v_x_1690_);
lean_dec(v_x_1690_);
lean_dec_ref(v_a_1689_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b1_1692_, lean_object* v_x_1693_, uint8_t v_isExporting_1694_, uint8_t v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_1693_, v_isExporting_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_x_1704_, lean_object* v_isExporting_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v_isExporting_boxed_1713_; uint8_t v___y_31109__boxed_1714_; lean_object* v_res_1715_; 
v_isExporting_boxed_1713_ = lean_unbox(v_isExporting_1705_);
v___y_31109__boxed_1714_ = lean_unbox(v___y_1706_);
v_res_1715_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(v_00_u03b1_1703_, v_x_1704_, v_isExporting_boxed_1713_, v___y_31109__boxed_1714_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(lean_object* v_00_u03b1_1716_, lean_object* v_x_1717_, uint8_t v_when_1718_, uint8_t v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_1717_, v_when_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1727_, lean_object* v_x_1728_, lean_object* v_when_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v_when_boxed_1737_; uint8_t v___y_31132__boxed_1738_; lean_object* v_res_1739_; 
v_when_boxed_1737_ = lean_unbox(v_when_1729_);
v___y_31132__boxed_1738_ = lean_unbox(v___y_1730_);
v_res_1739_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(v_00_u03b1_1727_, v_x_1728_, v_when_boxed_1737_, v___y_31132__boxed_1738_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9(lean_object* v_00_u03b2_1740_, lean_object* v_x_1741_, size_t v_x_1742_, size_t v_x_1743_, lean_object* v_x_1744_, lean_object* v_x_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_1741_, v_x_1742_, v_x_1743_, v_x_1744_, v_x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
size_t v_x_31156__boxed_1753_; size_t v_x_31157__boxed_1754_; lean_object* v_res_1755_; 
v_x_31156__boxed_1753_ = lean_unbox_usize(v_x_1749_);
lean_dec(v_x_1749_);
v_x_31157__boxed_1754_ = lean_unbox_usize(v_x_1750_);
lean_dec(v_x_1750_);
v_res_1755_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9(v_00_u03b2_1747_, v_x_1748_, v_x_31156__boxed_1753_, v_x_31157__boxed_1754_, v_x_1751_, v_x_1752_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1756_, lean_object* v_i_1757_, lean_object* v_source_1758_, lean_object* v_target_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(v_i_1757_, v_source_1758_, v_target_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15(lean_object* v_00_u03b2_1761_, lean_object* v_n_1762_, lean_object* v_k_1763_, lean_object* v_v_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(v_n_1762_, v_k_1763_, v_v_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16(lean_object* v_00_u03b2_1766_, size_t v_depth_1767_, lean_object* v_keys_1768_, lean_object* v_vals_1769_, lean_object* v_heq_1770_, lean_object* v_i_1771_, lean_object* v_entries_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_depth_1767_, v_keys_1768_, v_vals_1769_, v_i_1771_, v_entries_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1774_, lean_object* v_depth_1775_, lean_object* v_keys_1776_, lean_object* v_vals_1777_, lean_object* v_heq_1778_, lean_object* v_i_1779_, lean_object* v_entries_1780_){
_start:
{
size_t v_depth_boxed_1781_; lean_object* v_res_1782_; 
v_depth_boxed_1781_ = lean_unbox_usize(v_depth_1775_);
lean_dec(v_depth_1775_);
v_res_1782_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16(v_00_u03b2_1774_, v_depth_boxed_1781_, v_keys_1776_, v_vals_1777_, v_heq_1778_, v_i_1779_, v_entries_1780_);
lean_dec_ref(v_vals_1777_);
lean_dec_ref(v_keys_1776_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1783_, lean_object* v_x_1784_, lean_object* v_x_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(v_x_1784_, v_x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19(lean_object* v_00_u03b2_1787_, lean_object* v_x_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(v_x_1788_, v_x_1789_, v_x_1790_, v_x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__0(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_box(0);
v___x_1794_ = lean_unsigned_to_nat(16u);
v___x_1795_ = lean_mk_array(v___x_1794_, v___x_1793_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__1(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__0, &l_Lean_Meta_abstractNestedProofs___closed__0_once, _init_l_Lean_Meta_abstractNestedProofs___closed__0);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
lean_ctor_set(v___x_1798_, 1, v___x_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs(lean_object* v_e_1799_, uint8_t v_cache_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1806_; 
lean_inc_ref(v_e_1799_);
v___x_1806_ = l_Lean_Meta_isProof(v_e_1799_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1827_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1827_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1827_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_unbox(v_a_1807_);
lean_dec(v_a_1807_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_del_object(v___x_1809_);
v___x_1812_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__1, &l_Lean_Meta_abstractNestedProofs___closed__1_once, _init_l_Lean_Meta_abstractNestedProofs___closed__1);
v___x_1813_ = lean_st_mk_ref(v___x_1812_);
v___x_1814_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1799_, v_cache_1800_, v___x_1813_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1823_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = lean_st_ref_get(v___x_1813_);
lean_dec(v___x_1813_);
lean_dec(v___x_1819_);
if (v_isShared_1818_ == 0)
{
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1815_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_dec(v___x_1813_);
return v___x_1814_;
}
}
else
{
lean_object* v___x_1825_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v_e_1799_);
v___x_1825_ = v___x_1809_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_e_1799_);
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
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec_ref(v_e_1799_);
v_a_1828_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1806_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1806_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object* v_e_1836_, lean_object* v_cache_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
uint8_t v_cache_boxed_1843_; lean_object* v_res_1844_; 
v_cache_boxed_1843_ = lean_unbox(v_cache_1837_);
v_res_1844_ = l_Lean_Meta_abstractNestedProofs(v_e_1836_, v_cache_boxed_1843_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
return v_res_1844_;
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
