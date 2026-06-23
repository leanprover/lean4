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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0;
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
lean_dec_ref_known(v_r_339_, 1);
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
uint8_t v___y_29297__boxed_502_; lean_object* v_res_503_; 
v___y_29297__boxed_502_ = lean_unbox(v___y_495_);
v_res_503_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(v_x_494_, v___y_29297__boxed_502_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
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
uint8_t v___y_29322__boxed_535_; lean_object* v_res_536_; 
v___y_29322__boxed_535_ = lean_unbox(v___y_528_);
v_res_536_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_lctx_525_, v_localInsts_526_, v_x_527_, v___y_29322__boxed_535_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
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
uint8_t v___y_29366__boxed_560_; lean_object* v_res_561_; 
v___y_29366__boxed_560_ = lean_unbox(v___y_553_);
v_res_561_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_00_u03b1_549_, v_lctx_550_, v_localInsts_551_, v_x_552_, v___y_29366__boxed_560_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
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
uint8_t v___y_29389__boxed_584_; lean_object* v_res_585_; 
v___y_29389__boxed_584_ = lean_unbox(v___y_575_);
v_res_585_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(v_k_574_, v___y_29389__boxed_584_, v___y_576_, v_b_577_, v_c_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
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
uint8_t v_cleanupAnnotations_boxed_622_; uint8_t v_preserveNondepLet_boxed_623_; uint8_t v___y_29414__boxed_624_; lean_object* v_res_625_; 
v_cleanupAnnotations_boxed_622_ = lean_unbox(v_cleanupAnnotations_613_);
v_preserveNondepLet_boxed_623_ = lean_unbox(v_preserveNondepLet_614_);
v___y_29414__boxed_624_ = lean_unbox(v___y_615_);
v_res_625_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_611_, v_k_612_, v_cleanupAnnotations_boxed_622_, v_preserveNondepLet_boxed_623_, v___y_29414__boxed_624_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
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
uint8_t v_cleanupAnnotations_boxed_651_; uint8_t v_preserveNondepLet_boxed_652_; uint8_t v___y_29464__boxed_653_; lean_object* v_res_654_; 
v_cleanupAnnotations_boxed_651_ = lean_unbox(v_cleanupAnnotations_642_);
v_preserveNondepLet_boxed_652_ = lean_unbox(v_preserveNondepLet_643_);
v___y_29464__boxed_653_ = lean_unbox(v___y_644_);
v_res_654_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(v_00_u03b1_639_, v_e_640_, v_k_641_, v_cleanupAnnotations_boxed_651_, v_preserveNondepLet_boxed_652_, v___y_29464__boxed_653_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
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
uint8_t v_cleanupAnnotations_boxed_688_; uint8_t v___y_29487__boxed_689_; lean_object* v_res_690_; 
v_cleanupAnnotations_boxed_688_ = lean_unbox(v_cleanupAnnotations_680_);
v___y_29487__boxed_689_ = lean_unbox(v___y_681_);
v_res_690_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_678_, v_k_679_, v_cleanupAnnotations_boxed_688_, v___y_29487__boxed_689_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
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
uint8_t v_cleanupAnnotations_boxed_714_; uint8_t v___y_29535__boxed_715_; lean_object* v_res_716_; 
v_cleanupAnnotations_boxed_714_ = lean_unbox(v_cleanupAnnotations_706_);
v___y_29535__boxed_715_ = lean_unbox(v___y_707_);
v_res_716_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_00_u03b1_703_, v_type_704_, v_k_705_, v_cleanupAnnotations_boxed_714_, v___y_29535__boxed_715_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(lean_object* v_x_753_, size_t v_x_754_, size_t v_x_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
lean_object* v_es_758_; size_t v___x_759_; size_t v___x_760_; lean_object* v_j_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_es_758_ = lean_ctor_get(v_x_753_, 0);
v___x_759_ = ((size_t)31ULL);
v___x_760_ = lean_usize_land(v_x_754_, v___x_759_);
v_j_761_ = lean_usize_to_nat(v___x_760_);
v___x_762_ = lean_array_get_size(v_es_758_);
v___x_763_ = lean_nat_dec_lt(v_j_761_, v___x_762_);
if (v___x_763_ == 0)
{
lean_dec(v_j_761_);
lean_dec(v_x_757_);
lean_dec(v_x_756_);
return v_x_753_;
}
else
{
lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_802_; 
lean_inc_ref(v_es_758_);
v_isSharedCheck_802_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_803_);
v___x_765_ = v_x_753_;
v_isShared_766_ = v_isSharedCheck_802_;
goto v_resetjp_764_;
}
else
{
lean_dec(v_x_753_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_802_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v_v_767_; lean_object* v___x_768_; lean_object* v_xs_x27_769_; lean_object* v___y_771_; 
v_v_767_ = lean_array_fget(v_es_758_, v_j_761_);
v___x_768_ = lean_box(0);
v_xs_x27_769_ = lean_array_fset(v_es_758_, v_j_761_, v___x_768_);
switch(lean_obj_tag(v_v_767_))
{
case 0:
{
lean_object* v_key_776_; lean_object* v_val_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_787_; 
v_key_776_ = lean_ctor_get(v_v_767_, 0);
v_val_777_ = lean_ctor_get(v_v_767_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_v_767_);
if (v_isSharedCheck_787_ == 0)
{
v___x_779_ = v_v_767_;
v_isShared_780_ = v_isSharedCheck_787_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_val_777_);
lean_inc(v_key_776_);
lean_dec(v_v_767_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_787_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
uint8_t v___x_781_; 
v___x_781_ = l_Lean_instBEqFVarId_beq(v_x_756_, v_key_776_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_del_object(v___x_779_);
v___x_782_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_776_, v_val_777_, v_x_756_, v_x_757_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
v___y_771_ = v___x_783_;
goto v___jp_770_;
}
else
{
lean_object* v___x_785_; 
lean_dec(v_val_777_);
lean_dec(v_key_776_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v_x_757_);
lean_ctor_set(v___x_779_, 0, v_x_756_);
v___x_785_ = v___x_779_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_x_756_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_x_757_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
v___y_771_ = v___x_785_;
goto v___jp_770_;
}
}
}
}
case 1:
{
lean_object* v_node_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_800_; 
v_node_788_ = lean_ctor_get(v_v_767_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v_v_767_);
if (v_isSharedCheck_800_ == 0)
{
v___x_790_ = v_v_767_;
v_isShared_791_ = v_isSharedCheck_800_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_node_788_);
lean_dec(v_v_767_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_800_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; size_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_792_ = ((size_t)5ULL);
v___x_793_ = lean_usize_shift_right(v_x_754_, v___x_792_);
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_add(v_x_755_, v___x_794_);
v___x_796_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_node_788_, v___x_793_, v___x_795_, v_x_756_, v_x_757_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_796_);
v___x_798_ = v___x_790_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
v___y_771_ = v___x_798_;
goto v___jp_770_;
}
}
}
default: 
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_x_756_);
lean_ctor_set(v___x_801_, 1, v_x_757_);
v___y_771_ = v___x_801_;
goto v___jp_770_;
}
}
v___jp_770_:
{
lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_772_ = lean_array_fset(v_xs_x27_769_, v_j_761_, v___y_771_);
lean_dec(v_j_761_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_772_);
v___x_774_ = v___x_765_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
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
else
{
lean_object* v_ks_804_; lean_object* v_vs_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_825_; 
v_ks_804_ = lean_ctor_get(v_x_753_, 0);
v_vs_805_ = lean_ctor_get(v_x_753_, 1);
v_isSharedCheck_825_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_825_ == 0)
{
v___x_807_ = v_x_753_;
v_isShared_808_ = v_isSharedCheck_825_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_vs_805_);
lean_inc(v_ks_804_);
lean_dec(v_x_753_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_825_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_ks_804_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_vs_805_);
v___x_810_ = v_reuseFailAlloc_824_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v_newNode_811_; uint8_t v___y_813_; size_t v___x_819_; uint8_t v___x_820_; 
v_newNode_811_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(v___x_810_, v_x_756_, v_x_757_);
v___x_819_ = ((size_t)7ULL);
v___x_820_ = lean_usize_dec_le(v___x_819_, v_x_755_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_821_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_811_);
v___x_822_ = lean_unsigned_to_nat(4u);
v___x_823_ = lean_nat_dec_lt(v___x_821_, v___x_822_);
lean_dec(v___x_821_);
v___y_813_ = v___x_823_;
goto v___jp_812_;
}
else
{
v___y_813_ = v___x_820_;
goto v___jp_812_;
}
v___jp_812_:
{
if (v___y_813_ == 0)
{
lean_object* v_ks_814_; lean_object* v_vs_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_ks_814_ = lean_ctor_get(v_newNode_811_, 0);
lean_inc_ref(v_ks_814_);
v_vs_815_ = lean_ctor_get(v_newNode_811_, 1);
lean_inc_ref(v_vs_815_);
lean_dec_ref(v_newNode_811_);
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0);
v___x_818_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_x_755_, v_ks_814_, v_vs_815_, v___x_816_, v___x_817_);
lean_dec_ref(v_vs_815_);
lean_dec_ref(v_ks_814_);
return v___x_818_;
}
else
{
return v_newNode_811_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(size_t v_depth_826_, lean_object* v_keys_827_, lean_object* v_vals_828_, lean_object* v_i_829_, lean_object* v_entries_830_){
_start:
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = lean_array_get_size(v_keys_827_);
v___x_832_ = lean_nat_dec_lt(v_i_829_, v___x_831_);
if (v___x_832_ == 0)
{
lean_dec(v_i_829_);
return v_entries_830_;
}
else
{
lean_object* v_k_833_; lean_object* v_v_834_; uint64_t v___x_835_; size_t v_h_836_; size_t v___x_837_; lean_object* v___x_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; size_t v_h_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_k_833_ = lean_array_fget_borrowed(v_keys_827_, v_i_829_);
v_v_834_ = lean_array_fget_borrowed(v_vals_828_, v_i_829_);
v___x_835_ = l_Lean_instHashableFVarId_hash(v_k_833_);
v_h_836_ = lean_uint64_to_usize(v___x_835_);
v___x_837_ = ((size_t)5ULL);
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_sub(v_depth_826_, v___x_839_);
v___x_841_ = lean_usize_mul(v___x_837_, v___x_840_);
v_h_842_ = lean_usize_shift_right(v_h_836_, v___x_841_);
v___x_843_ = lean_nat_add(v_i_829_, v___x_838_);
lean_dec(v_i_829_);
lean_inc(v_v_834_);
lean_inc(v_k_833_);
v___x_844_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_entries_830_, v_h_842_, v_depth_826_, v_k_833_, v_v_834_);
v_i_829_ = v___x_843_;
v_entries_830_ = v___x_844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg___boxed(lean_object* v_depth_846_, lean_object* v_keys_847_, lean_object* v_vals_848_, lean_object* v_i_849_, lean_object* v_entries_850_){
_start:
{
size_t v_depth_boxed_851_; lean_object* v_res_852_; 
v_depth_boxed_851_ = lean_unbox_usize(v_depth_846_);
lean_dec(v_depth_846_);
v_res_852_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_depth_boxed_851_, v_keys_847_, v_vals_848_, v_i_849_, v_entries_850_);
lean_dec_ref(v_vals_848_);
lean_dec_ref(v_keys_847_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___boxed(lean_object* v_x_853_, lean_object* v_x_854_, lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
size_t v_x_29635__boxed_858_; size_t v_x_29636__boxed_859_; lean_object* v_res_860_; 
v_x_29635__boxed_858_ = lean_unbox_usize(v_x_854_);
lean_dec(v_x_854_);
v_x_29636__boxed_859_ = lean_unbox_usize(v_x_855_);
lean_dec(v_x_855_);
v_res_860_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_853_, v_x_29635__boxed_858_, v_x_29636__boxed_859_, v_x_856_, v_x_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
uint64_t v___x_864_; size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_864_ = l_Lean_instHashableFVarId_hash(v_x_862_);
v___x_865_ = lean_uint64_to_usize(v___x_864_);
v___x_866_ = ((size_t)1ULL);
v___x_867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_861_, v___x_865_, v___x_866_, v_x_862_, v_x_863_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(lean_object* v_a_868_, lean_object* v_x_869_){
_start:
{
if (lean_obj_tag(v_x_869_) == 0)
{
lean_object* v___x_870_; 
v___x_870_ = lean_box(0);
return v___x_870_;
}
else
{
lean_object* v_key_871_; lean_object* v_value_872_; lean_object* v_tail_873_; uint8_t v___x_874_; 
v_key_871_ = lean_ctor_get(v_x_869_, 0);
v_value_872_ = lean_ctor_get(v_x_869_, 1);
v_tail_873_ = lean_ctor_get(v_x_869_, 2);
v___x_874_ = l_Lean_ExprStructEq_beq(v_key_871_, v_a_868_);
if (v___x_874_ == 0)
{
v_x_869_ = v_tail_873_;
goto _start;
}
else
{
lean_object* v___x_876_; 
lean_inc(v_value_872_);
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v_value_872_);
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg___boxed(lean_object* v_a_877_, lean_object* v_x_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_877_, v_x_878_);
lean_dec(v_x_878_);
lean_dec_ref(v_a_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(lean_object* v_m_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_buckets_882_; lean_object* v___x_883_; uint64_t v___x_884_; uint64_t v___x_885_; uint64_t v___x_886_; uint64_t v_fold_887_; uint64_t v___x_888_; uint64_t v___x_889_; uint64_t v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; size_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_buckets_882_ = lean_ctor_get(v_m_880_, 1);
v___x_883_ = lean_array_get_size(v_buckets_882_);
v___x_884_ = l_Lean_ExprStructEq_hash(v_a_881_);
v___x_885_ = 32ULL;
v___x_886_ = lean_uint64_shift_right(v___x_884_, v___x_885_);
v_fold_887_ = lean_uint64_xor(v___x_884_, v___x_886_);
v___x_888_ = 16ULL;
v___x_889_ = lean_uint64_shift_right(v_fold_887_, v___x_888_);
v___x_890_ = lean_uint64_xor(v_fold_887_, v___x_889_);
v___x_891_ = lean_uint64_to_usize(v___x_890_);
v___x_892_ = lean_usize_of_nat(v___x_883_);
v___x_893_ = ((size_t)1ULL);
v___x_894_ = lean_usize_sub(v___x_892_, v___x_893_);
v___x_895_ = lean_usize_land(v___x_891_, v___x_894_);
v___x_896_ = lean_array_uget_borrowed(v_buckets_882_, v___x_895_);
v___x_897_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_881_, v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg___boxed(lean_object* v_m_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_898_, v_a_899_);
lean_dec_ref(v_a_899_);
lean_dec_ref(v_m_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(lean_object* v_x_901_, uint8_t v_isExporting_902_, uint8_t v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___x_910_; lean_object* v_env_911_; uint8_t v_isExporting_912_; lean_object* v___x_913_; lean_object* v_env_914_; lean_object* v_nextMacroScope_915_; lean_object* v_ngen_916_; lean_object* v_auxDeclNGen_917_; lean_object* v_traceState_918_; lean_object* v_messages_919_; lean_object* v_infoState_920_; lean_object* v_snapshotTasks_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_976_; 
v___x_910_ = lean_st_ref_get(v___y_908_);
v_env_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc_ref(v_env_911_);
lean_dec(v___x_910_);
v_isExporting_912_ = lean_ctor_get_uint8(v_env_911_, sizeof(void*)*8);
lean_dec_ref(v_env_911_);
v___x_913_ = lean_st_ref_take(v___y_908_);
v_env_914_ = lean_ctor_get(v___x_913_, 0);
v_nextMacroScope_915_ = lean_ctor_get(v___x_913_, 1);
v_ngen_916_ = lean_ctor_get(v___x_913_, 2);
v_auxDeclNGen_917_ = lean_ctor_get(v___x_913_, 3);
v_traceState_918_ = lean_ctor_get(v___x_913_, 4);
v_messages_919_ = lean_ctor_get(v___x_913_, 6);
v_infoState_920_ = lean_ctor_get(v___x_913_, 7);
v_snapshotTasks_921_ = lean_ctor_get(v___x_913_, 8);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v___x_913_, 5);
lean_dec(v_unused_977_);
v___x_923_ = v___x_913_;
v_isShared_924_ = v_isSharedCheck_976_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_snapshotTasks_921_);
lean_inc(v_infoState_920_);
lean_inc(v_messages_919_);
lean_inc(v_traceState_918_);
lean_inc(v_auxDeclNGen_917_);
lean_inc(v_ngen_916_);
lean_inc(v_nextMacroScope_915_);
lean_inc(v_env_914_);
lean_dec(v___x_913_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_976_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_925_ = l_Lean_Environment_setExporting(v_env_914_, v_isExporting_902_);
v___x_926_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 5, v___x_926_);
lean_ctor_set(v___x_923_, 0, v___x_925_);
v___x_928_ = v___x_923_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_nextMacroScope_915_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_ngen_916_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_auxDeclNGen_917_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_traceState_918_);
lean_ctor_set(v_reuseFailAlloc_975_, 5, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_975_, 6, v_messages_919_);
lean_ctor_set(v_reuseFailAlloc_975_, 7, v_infoState_920_);
lean_ctor_set(v_reuseFailAlloc_975_, 8, v_snapshotTasks_921_);
v___x_928_ = v_reuseFailAlloc_975_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_mctx_931_; lean_object* v_zetaDeltaFVarIds_932_; lean_object* v_postponed_933_; lean_object* v_diag_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_973_; 
v___x_929_ = lean_st_ref_set(v___y_908_, v___x_928_);
v___x_930_ = lean_st_ref_take(v___y_906_);
v_mctx_931_ = lean_ctor_get(v___x_930_, 0);
v_zetaDeltaFVarIds_932_ = lean_ctor_get(v___x_930_, 2);
v_postponed_933_ = lean_ctor_get(v___x_930_, 3);
v_diag_934_ = lean_ctor_get(v___x_930_, 4);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; 
v_unused_974_ = lean_ctor_get(v___x_930_, 1);
lean_dec(v_unused_974_);
v___x_936_ = v___x_930_;
v_isShared_937_ = v_isSharedCheck_973_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_diag_934_);
lean_inc(v_postponed_933_);
lean_inc(v_zetaDeltaFVarIds_932_);
lean_inc(v_mctx_931_);
lean_dec(v___x_930_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_973_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v___x_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_mctx_931_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_zetaDeltaFVarIds_932_);
lean_ctor_set(v_reuseFailAlloc_972_, 3, v_postponed_933_);
lean_ctor_set(v_reuseFailAlloc_972_, 4, v_diag_934_);
v___x_940_ = v_reuseFailAlloc_972_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v_r_943_; 
v___x_941_ = lean_st_ref_set(v___y_906_, v___x_940_);
v___x_942_ = lean_box(v___y_903_);
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
lean_inc(v___y_904_);
v_r_943_ = lean_apply_7(v_x_901_, v___x_942_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, lean_box(0));
if (lean_obj_tag(v_r_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_960_; 
v_a_944_ = lean_ctor_get(v_r_943_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_r_943_);
if (v_isSharedCheck_960_ == 0)
{
v___x_946_ = v_r_943_;
v_isShared_947_ = v_isSharedCheck_960_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v_r_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_960_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
lean_inc(v_a_944_);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 1);
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_959_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
v___x_950_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_908_, v_isExporting_912_, v___x_926_, v___y_906_, v___x_938_, v___x_949_);
lean_dec_ref(v___x_949_);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; 
v_unused_958_ = lean_ctor_get(v___x_950_, 0);
lean_dec(v_unused_958_);
v___x_952_ = v___x_950_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_dec(v___x_950_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v_a_944_);
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_944_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_a_961_ = lean_ctor_get(v_r_943_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v_r_943_, 1);
v___x_962_ = lean_box(0);
v___x_963_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_908_, v_isExporting_912_, v___x_926_, v___y_906_, v___x_938_, v___x_962_);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; 
v_unused_971_ = lean_ctor_get(v___x_963_, 0);
lean_dec(v_unused_971_);
v___x_965_ = v___x_963_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_dec(v___x_963_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 1);
lean_ctor_set(v___x_965_, 0, v_a_961_);
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_961_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg___boxed(lean_object* v_x_978_, lean_object* v_isExporting_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
uint8_t v_isExporting_boxed_987_; uint8_t v___y_29865__boxed_988_; lean_object* v_res_989_; 
v_isExporting_boxed_987_ = lean_unbox(v_isExporting_979_);
v___y_29865__boxed_988_ = lean_unbox(v___y_980_);
v_res_989_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_978_, v_isExporting_boxed_987_, v___y_29865__boxed_988_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(lean_object* v_x_990_, uint8_t v_when_991_, uint8_t v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
if (v_when_991_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_box(v___y_992_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc_ref(v___y_994_);
lean_inc(v___y_993_);
v___x_1000_ = lean_apply_7(v_x_990_, v___x_999_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, lean_box(0));
return v___x_1000_;
}
else
{
uint8_t v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = 0;
v___x_1002_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_990_, v___x_1001_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___boxed(lean_object* v_x_1003_, lean_object* v_when_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v_when_boxed_1012_; uint8_t v___y_29998__boxed_1013_; lean_object* v_res_1014_; 
v_when_boxed_1012_ = lean_unbox(v_when_1004_);
v___y_29998__boxed_1013_ = lean_unbox(v___y_1005_);
v_res_1014_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_1003_, v_when_boxed_1012_, v___y_29998__boxed_1013_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0(lean_object* v_proof_1015_, uint8_t v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
v___x_1023_ = lean_infer_type(v_proof_1015_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0___boxed(lean_object* v_proof_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
uint8_t v___y_30027__boxed_1032_; lean_object* v_res_1033_; 
v___y_30027__boxed_1032_ = lean_unbox(v___y_1025_);
v_res_1033_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0(v_proof_1024_, v___y_30027__boxed_1032_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object* v_proof_1034_, uint8_t v_cache_1035_, lean_object* v_postprocessType_1036_, uint8_t v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___f_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; 
lean_inc_ref(v_proof_1034_);
v___f_1044_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1044_, 0, v_proof_1034_);
v___x_1045_ = 1;
v___x_1046_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v___f_1044_, v___x_1045_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1048_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1048_ = l_Lean_Core_betaReduce(v_a_1047_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = l_Lean_Meta_zetaReduce(v_a_1049_, v___x_1045_, v___x_1045_, v___x_1045_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = lean_box(v___y_1037_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
v___x_1053_ = lean_apply_8(v_postprocessType_1036_, v_a_1051_, v___x_1052_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, lean_box(0));
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; uint8_t v___y_1056_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
if (v_cache_1035_ == 0)
{
v___y_1056_ = v_cache_1035_;
goto v___jp_1055_;
}
else
{
uint8_t v___x_1059_; 
v___x_1059_ = l_Lean_Expr_hasSorry(v_proof_1034_);
if (v___x_1059_ == 0)
{
v___y_1056_ = v_cache_1035_;
goto v___jp_1055_;
}
else
{
uint8_t v___x_1060_; 
v___x_1060_ = 0;
v___y_1056_ = v___x_1060_;
goto v___jp_1055_;
}
}
v___jp_1055_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = l_Lean_Meta_mkAuxTheorem(v_a_1054_, v_proof_1034_, v___x_1045_, v___x_1057_, v___y_1056_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v___x_1058_;
}
}
else
{
lean_dec_ref(v_proof_1034_);
return v___x_1053_;
}
}
else
{
lean_dec_ref(v_postprocessType_1036_);
lean_dec_ref(v_proof_1034_);
return v___x_1050_;
}
}
else
{
lean_dec_ref(v_postprocessType_1036_);
lean_dec_ref(v_proof_1034_);
return v___x_1048_;
}
}
else
{
lean_dec_ref(v_postprocessType_1036_);
lean_dec_ref(v_proof_1034_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object* v_proof_1061_, lean_object* v_cache_1062_, lean_object* v_postprocessType_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
uint8_t v_cache_boxed_1071_; uint8_t v___y_30050__boxed_1072_; lean_object* v_res_1073_; 
v_cache_boxed_1071_ = lean_unbox(v_cache_1062_);
v___y_30050__boxed_1072_ = lean_unbox(v___y_1064_);
v_res_1073_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_proof_1061_, v_cache_boxed_1071_, v_postprocessType_1063_, v___y_30050__boxed_1072_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
if (lean_obj_tag(v_x_1075_) == 0)
{
return v_x_1074_;
}
else
{
lean_object* v_key_1076_; lean_object* v_value_1077_; lean_object* v_tail_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1101_; 
v_key_1076_ = lean_ctor_get(v_x_1075_, 0);
v_value_1077_ = lean_ctor_get(v_x_1075_, 1);
v_tail_1078_ = lean_ctor_get(v_x_1075_, 2);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1080_ = v_x_1075_;
v_isShared_1081_ = v_isSharedCheck_1101_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_tail_1078_);
lean_inc(v_value_1077_);
lean_inc(v_key_1076_);
lean_dec(v_x_1075_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1101_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; uint64_t v___x_1083_; uint64_t v___x_1084_; uint64_t v___x_1085_; uint64_t v_fold_1086_; uint64_t v___x_1087_; uint64_t v___x_1088_; uint64_t v___x_1089_; size_t v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1082_ = lean_array_get_size(v_x_1074_);
v___x_1083_ = l_Lean_ExprStructEq_hash(v_key_1076_);
v___x_1084_ = 32ULL;
v___x_1085_ = lean_uint64_shift_right(v___x_1083_, v___x_1084_);
v_fold_1086_ = lean_uint64_xor(v___x_1083_, v___x_1085_);
v___x_1087_ = 16ULL;
v___x_1088_ = lean_uint64_shift_right(v_fold_1086_, v___x_1087_);
v___x_1089_ = lean_uint64_xor(v_fold_1086_, v___x_1088_);
v___x_1090_ = lean_uint64_to_usize(v___x_1089_);
v___x_1091_ = lean_usize_of_nat(v___x_1082_);
v___x_1092_ = ((size_t)1ULL);
v___x_1093_ = lean_usize_sub(v___x_1091_, v___x_1092_);
v___x_1094_ = lean_usize_land(v___x_1090_, v___x_1093_);
v___x_1095_ = lean_array_uget_borrowed(v_x_1074_, v___x_1094_);
lean_inc(v___x_1095_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 2, v___x_1095_);
v___x_1097_ = v___x_1080_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_key_1076_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_value_1077_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_array_uset(v_x_1074_, v___x_1094_, v___x_1097_);
v_x_1074_ = v___x_1098_;
v_x_1075_ = v_tail_1078_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(lean_object* v_i_1102_, lean_object* v_source_1103_, lean_object* v_target_1104_){
_start:
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = lean_array_get_size(v_source_1103_);
v___x_1106_ = lean_nat_dec_lt(v_i_1102_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_dec_ref(v_source_1103_);
lean_dec(v_i_1102_);
return v_target_1104_;
}
else
{
lean_object* v_es_1107_; lean_object* v___x_1108_; lean_object* v_source_1109_; lean_object* v_target_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_es_1107_ = lean_array_fget(v_source_1103_, v_i_1102_);
v___x_1108_ = lean_box(0);
v_source_1109_ = lean_array_fset(v_source_1103_, v_i_1102_, v___x_1108_);
v_target_1110_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(v_target_1104_, v_es_1107_);
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v_i_1102_, v___x_1111_);
lean_dec(v_i_1102_);
v_i_1102_ = v___x_1112_;
v_source_1103_ = v_source_1109_;
v_target_1104_ = v_target_1110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(lean_object* v_data_1114_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v_nbuckets_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1115_ = lean_array_get_size(v_data_1114_);
v___x_1116_ = lean_unsigned_to_nat(2u);
v_nbuckets_1117_ = lean_nat_mul(v___x_1115_, v___x_1116_);
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = lean_box(0);
v___x_1120_ = lean_mk_array(v_nbuckets_1117_, v___x_1119_);
v___x_1121_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(v___x_1118_, v_data_1114_, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object* v_a_1122_, lean_object* v_x_1123_){
_start:
{
if (lean_obj_tag(v_x_1123_) == 0)
{
uint8_t v___x_1124_; 
v___x_1124_ = 0;
return v___x_1124_;
}
else
{
lean_object* v_key_1125_; lean_object* v_tail_1126_; uint8_t v___x_1127_; 
v_key_1125_ = lean_ctor_get(v_x_1123_, 0);
v_tail_1126_ = lean_ctor_get(v_x_1123_, 2);
v___x_1127_ = l_Lean_ExprStructEq_beq(v_key_1125_, v_a_1122_);
if (v___x_1127_ == 0)
{
v_x_1123_ = v_tail_1126_;
goto _start;
}
else
{
return v___x_1127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_1129_, lean_object* v_x_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1129_, v_x_1130_);
lean_dec(v_x_1130_);
lean_dec_ref(v_a_1129_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(lean_object* v_a_1133_, lean_object* v_b_1134_, lean_object* v_x_1135_){
_start:
{
if (lean_obj_tag(v_x_1135_) == 0)
{
lean_dec(v_b_1134_);
lean_dec_ref(v_a_1133_);
return v_x_1135_;
}
else
{
lean_object* v_key_1136_; lean_object* v_value_1137_; lean_object* v_tail_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1150_; 
v_key_1136_ = lean_ctor_get(v_x_1135_, 0);
v_value_1137_ = lean_ctor_get(v_x_1135_, 1);
v_tail_1138_ = lean_ctor_get(v_x_1135_, 2);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_x_1135_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1140_ = v_x_1135_;
v_isShared_1141_ = v_isSharedCheck_1150_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_tail_1138_);
lean_inc(v_value_1137_);
lean_inc(v_key_1136_);
lean_dec(v_x_1135_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1150_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
uint8_t v___x_1142_; 
v___x_1142_ = l_Lean_ExprStructEq_beq(v_key_1136_, v_a_1133_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1133_, v_b_1134_, v_tail_1138_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 2, v___x_1143_);
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_key_1136_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_value_1137_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
else
{
lean_object* v___x_1148_; 
lean_dec(v_value_1137_);
lean_dec(v_key_1136_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v_b_1134_);
lean_ctor_set(v___x_1140_, 0, v_a_1133_);
v___x_1148_ = v___x_1140_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1133_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_b_1134_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_tail_1138_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object* v_m_1151_, lean_object* v_a_1152_, lean_object* v_b_1153_){
_start:
{
lean_object* v_size_1154_; lean_object* v_buckets_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1198_; 
v_size_1154_ = lean_ctor_get(v_m_1151_, 0);
v_buckets_1155_ = lean_ctor_get(v_m_1151_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_m_1151_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1157_ = v_m_1151_;
v_isShared_1158_ = v_isSharedCheck_1198_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_buckets_1155_);
lean_inc(v_size_1154_);
lean_dec(v_m_1151_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1198_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; uint64_t v___x_1160_; uint64_t v___x_1161_; uint64_t v___x_1162_; uint64_t v_fold_1163_; uint64_t v___x_1164_; uint64_t v___x_1165_; uint64_t v___x_1166_; size_t v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; size_t v___x_1170_; size_t v___x_1171_; lean_object* v_bkt_1172_; uint8_t v___x_1173_; 
v___x_1159_ = lean_array_get_size(v_buckets_1155_);
v___x_1160_ = l_Lean_ExprStructEq_hash(v_a_1152_);
v___x_1161_ = 32ULL;
v___x_1162_ = lean_uint64_shift_right(v___x_1160_, v___x_1161_);
v_fold_1163_ = lean_uint64_xor(v___x_1160_, v___x_1162_);
v___x_1164_ = 16ULL;
v___x_1165_ = lean_uint64_shift_right(v_fold_1163_, v___x_1164_);
v___x_1166_ = lean_uint64_xor(v_fold_1163_, v___x_1165_);
v___x_1167_ = lean_uint64_to_usize(v___x_1166_);
v___x_1168_ = lean_usize_of_nat(v___x_1159_);
v___x_1169_ = ((size_t)1ULL);
v___x_1170_ = lean_usize_sub(v___x_1168_, v___x_1169_);
v___x_1171_ = lean_usize_land(v___x_1167_, v___x_1170_);
v_bkt_1172_ = lean_array_uget_borrowed(v_buckets_1155_, v___x_1171_);
v___x_1173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1152_, v_bkt_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v_size_x27_1175_; lean_object* v___x_1176_; lean_object* v_buckets_x27_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
v_size_x27_1175_ = lean_nat_add(v_size_1154_, v___x_1174_);
lean_dec(v_size_1154_);
lean_inc(v_bkt_1172_);
v___x_1176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1176_, 0, v_a_1152_);
lean_ctor_set(v___x_1176_, 1, v_b_1153_);
lean_ctor_set(v___x_1176_, 2, v_bkt_1172_);
v_buckets_x27_1177_ = lean_array_uset(v_buckets_1155_, v___x_1171_, v___x_1176_);
v___x_1178_ = lean_unsigned_to_nat(4u);
v___x_1179_ = lean_nat_mul(v_size_x27_1175_, v___x_1178_);
v___x_1180_ = lean_unsigned_to_nat(3u);
v___x_1181_ = lean_nat_div(v___x_1179_, v___x_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_array_get_size(v_buckets_x27_1177_);
v___x_1183_ = lean_nat_dec_le(v___x_1181_, v___x_1182_);
lean_dec(v___x_1181_);
if (v___x_1183_ == 0)
{
lean_object* v_val_1184_; lean_object* v___x_1186_; 
v_val_1184_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(v_buckets_x27_1177_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v_val_1184_);
lean_ctor_set(v___x_1157_, 0, v_size_x27_1175_);
v___x_1186_ = v___x_1157_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_size_x27_1175_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_val_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
else
{
lean_object* v___x_1189_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v_buckets_x27_1177_);
lean_ctor_set(v___x_1157_, 0, v_size_x27_1175_);
v___x_1189_ = v___x_1157_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_size_x27_1175_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_buckets_x27_1177_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
lean_object* v___x_1191_; lean_object* v_buckets_x27_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
lean_inc(v_bkt_1172_);
v___x_1191_ = lean_box(0);
v_buckets_x27_1192_ = lean_array_uset(v_buckets_1155_, v___x_1171_, v___x_1191_);
v___x_1193_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1152_, v_b_1153_, v_bkt_1172_);
v___x_1194_ = lean_array_uset(v_buckets_x27_1192_, v___x_1171_, v___x_1193_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v___x_1194_);
v___x_1196_ = v___x_1157_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_size_1154_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object* v_e_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
uint8_t v_a_boxed_1208_; lean_object* v_res_1209_; 
v_a_boxed_1208_ = lean_unbox(v_a_1201_);
v_res_1209_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1200_, v_a_boxed_1208_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object* v_as_1210_, size_t v_sz_1211_, size_t v_i_1212_, lean_object* v_b_1213_, uint8_t v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_a_1222_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; uint8_t v___x_1235_; 
v___x_1235_ = lean_usize_dec_lt(v_i_1212_, v_sz_1211_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_b_1213_);
return v___x_1236_;
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1238_; lean_object* v_localDecl_1240_; lean_object* v___x_1248_; 
v_a_1237_ = lean_array_uget_borrowed(v_as_1210_, v_i_1212_);
v___x_1238_ = l_Lean_Expr_fvarId_x21(v_a_1237_);
lean_inc(v___x_1238_);
v___x_1248_ = l_Lean_FVarId_getDecl___redArg(v___x_1238_, v___y_1216_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1250_ = l_Lean_LocalDecl_type(v_a_1249_);
v___x_1251_ = l_Lean_Meta_AbstractNestedProofs_visit(v___x_1250_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v___x_1253_ = l_Lean_LocalDecl_setType(v_a_1249_, v_a_1252_);
v___x_1254_ = l_Lean_LocalDecl_value_x3f(v___x_1253_, v___x_1235_);
if (lean_obj_tag(v___x_1254_) == 0)
{
v_localDecl_1240_ = v___x_1253_;
goto v___jp_1239_;
}
else
{
lean_object* v_val_1255_; lean_object* v___x_1256_; 
v_val_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_val_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = l_Lean_Meta_AbstractNestedProofs_visit(v_val_1255_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = l_Lean_LocalDecl_setValue(v___x_1253_, v_a_1257_);
v_localDecl_1240_ = v___x_1258_;
goto v___jp_1239_;
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v___x_1253_);
lean_dec(v___x_1238_);
lean_dec_ref(v_b_1213_);
v_a_1259_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1256_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1256_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v_a_1249_);
lean_dec(v___x_1238_);
lean_dec_ref(v_b_1213_);
v_a_1267_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1251_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1251_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v___x_1238_);
lean_dec_ref(v_b_1213_);
v_a_1275_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1248_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1248_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
v___jp_1239_:
{
lean_object* v_fvarIdToDecl_1241_; lean_object* v_decls_1242_; lean_object* v_auxDeclToFullName_1243_; lean_object* v___x_1244_; 
v_fvarIdToDecl_1241_ = lean_ctor_get(v_b_1213_, 0);
v_decls_1242_ = lean_ctor_get(v_b_1213_, 1);
v_auxDeclToFullName_1243_ = lean_ctor_get(v_b_1213_, 2);
lean_inc_ref(v_b_1213_);
v___x_1244_ = lean_local_ctx_find(v_b_1213_, v___x_1238_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_dec_ref(v_localDecl_1240_);
v_a_1222_ = v_b_1213_;
goto v___jp_1221_;
}
else
{
lean_object* v_index_1245_; lean_object* v_fvarId_1246_; lean_object* v___x_1247_; 
lean_inc(v_auxDeclToFullName_1243_);
lean_inc_ref(v_decls_1242_);
lean_inc_ref(v_fvarIdToDecl_1241_);
lean_dec_ref_known(v___x_1244_, 1);
lean_dec_ref(v_b_1213_);
v_index_1245_ = lean_ctor_get(v_localDecl_1240_, 0);
lean_inc(v_index_1245_);
v_fvarId_1246_ = lean_ctor_get(v_localDecl_1240_, 1);
lean_inc_ref(v_localDecl_1240_);
lean_inc(v_fvarId_1246_);
v___x_1247_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_fvarIdToDecl_1241_, v_fvarId_1246_, v_localDecl_1240_);
v___y_1227_ = v_decls_1242_;
v___y_1228_ = v_localDecl_1240_;
v___y_1229_ = v_auxDeclToFullName_1243_;
v___y_1230_ = v___x_1247_;
v___y_1231_ = v_index_1245_;
goto v___jp_1226_;
}
}
}
v___jp_1221_:
{
size_t v___x_1223_; size_t v___x_1224_; 
v___x_1223_ = ((size_t)1ULL);
v___x_1224_ = lean_usize_add(v_i_1212_, v___x_1223_);
v_i_1212_ = v___x_1224_;
v_b_1213_ = v_a_1222_;
goto _start;
}
v___jp_1226_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___y_1228_);
v___x_1233_ = l_Lean_PersistentArray_set___redArg(v___y_1227_, v___y_1231_, v___x_1232_);
lean_dec(v___y_1231_);
v___x_1234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1234_, 0, v___y_1230_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
lean_ctor_set(v___x_1234_, 2, v___y_1229_);
v_a_1222_ = v___x_1234_;
goto v___jp_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object* v_xs_1283_, lean_object* v_k_1284_, uint8_t v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_lctx_1292_; lean_object* v_localInstances_1293_; size_t v_sz_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v_lctx_1292_ = lean_ctor_get(v___y_1287_, 2);
v_localInstances_1293_ = lean_ctor_get(v___y_1287_, 3);
v_sz_1294_ = lean_array_size(v_xs_1283_);
v___x_1295_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1292_);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_xs_1283_, v_sz_1294_, v___x_1295_, v_lctx_1292_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1298_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
lean_inc_ref(v_localInstances_1293_);
v___x_1298_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_a_1297_, v_localInstances_1293_, v_k_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1298_;
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref(v_k_1284_);
v_a_1299_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1296_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1296_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object* v_xs_1307_, lean_object* v_k_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v___y_30365__boxed_1316_; lean_object* v_res_1317_; 
v___y_30365__boxed_1316_ = lean_unbox(v___y_1309_);
v_res_1317_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(v_xs_1307_, v_k_1308_, v___y_30365__boxed_1316_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v_xs_1307_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object* v___y_1318_, lean_object* v___f_1319_, lean_object* v_xs_1320_, lean_object* v_b_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
uint8_t v___y_30315__boxed_1329_; uint8_t v___y_30317__boxed_1330_; lean_object* v_res_1331_; 
v___y_30315__boxed_1329_ = lean_unbox(v___y_1318_);
v___y_30317__boxed_1330_ = lean_unbox(v___y_1322_);
v_res_1331_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(v___y_30315__boxed_1329_, v___f_1319_, v_xs_1320_, v_b_1321_, v___y_30317__boxed_1330_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object* v_b_1332_, lean_object* v_xs_1333_, uint8_t v___y_1334_, uint8_t v___x_1335_, uint8_t v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1332_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; uint8_t v___x_1345_; lean_object* v___x_1346_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = 1;
v___x_1346_ = l_Lean_Meta_mkForallFVars(v_xs_1333_, v_a_1344_, v___y_1334_, v___x_1335_, v___x_1335_, v___x_1345_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
return v___x_1346_;
}
else
{
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object* v_b_1347_, lean_object* v_xs_1348_, lean_object* v___y_1349_, lean_object* v___x_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v___y_30351__boxed_1358_; uint8_t v___x_30352__boxed_1359_; uint8_t v___y_30353__boxed_1360_; lean_object* v_res_1361_; 
v___y_30351__boxed_1358_ = lean_unbox(v___y_1349_);
v___x_30352__boxed_1359_ = lean_unbox(v___x_1350_);
v___y_30353__boxed_1360_ = lean_unbox(v___y_1351_);
v_res_1361_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(v_b_1347_, v_xs_1348_, v___y_30351__boxed_1358_, v___x_30352__boxed_1359_, v___y_30353__boxed_1360_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v_xs_1348_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t v___y_1362_, uint8_t v___x_1363_, lean_object* v___f_1364_, lean_object* v_xs_1365_, lean_object* v_b_1366_, uint8_t v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___f_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1374_ = lean_box(v___y_1362_);
v___x_1375_ = lean_box(v___x_1363_);
lean_inc_ref(v_xs_1365_);
v___f_1376_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1376_, 0, v_b_1366_);
lean_closure_set(v___f_1376_, 1, v_xs_1365_);
lean_closure_set(v___f_1376_, 2, v___x_1374_);
lean_closure_set(v___f_1376_, 3, v___x_1375_);
v___x_1377_ = lean_box(v___y_1367_);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
v___x_1378_ = lean_apply_9(v___f_1364_, v_xs_1365_, v___f_1376_, v___x_1377_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object* v___y_1379_, lean_object* v___x_1380_, lean_object* v___f_1381_, lean_object* v_xs_1382_, lean_object* v_b_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v___y_30326__boxed_1391_; uint8_t v___x_30327__boxed_1392_; uint8_t v___y_30329__boxed_1393_; lean_object* v_res_1394_; 
v___y_30326__boxed_1391_ = lean_unbox(v___y_1379_);
v___x_30327__boxed_1392_ = lean_unbox(v___x_1380_);
v___y_30329__boxed_1393_ = lean_unbox(v___y_1384_);
v_res_1394_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(v___y_30326__boxed_1391_, v___x_30327__boxed_1392_, v___f_1381_, v_xs_1382_, v_b_1383_, v___y_30329__boxed_1393_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t v_sz_1395_, size_t v_i_1396_, lean_object* v_bs_1397_, uint8_t v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v___x_1405_; 
v___x_1405_ = lean_usize_dec_lt(v_i_1396_, v_sz_1395_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v_bs_1397_);
return v___x_1406_;
}
else
{
lean_object* v_v_1407_; lean_object* v___x_1408_; 
v_v_1407_ = lean_array_uget_borrowed(v_bs_1397_, v_i_1396_);
lean_inc(v_v_1407_);
v___x_1408_ = l_Lean_Meta_AbstractNestedProofs_visit(v_v_1407_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1410_; lean_object* v_bs_x27_1411_; size_t v___x_1412_; size_t v___x_1413_; lean_object* v___x_1414_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1408_, 1);
v___x_1410_ = lean_unsigned_to_nat(0u);
v_bs_x27_1411_ = lean_array_uset(v_bs_1397_, v_i_1396_, v___x_1410_);
v___x_1412_ = ((size_t)1ULL);
v___x_1413_ = lean_usize_add(v_i_1396_, v___x_1412_);
v___x_1414_ = lean_array_uset(v_bs_x27_1411_, v_i_1396_, v_a_1409_);
v_i_1396_ = v___x_1413_;
v_bs_1397_ = v___x_1414_;
goto _start;
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v_bs_1397_);
v_a_1416_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1408_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1408_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object* v_x_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_, uint8_t v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
if (lean_obj_tag(v_x_1424_) == 5)
{
lean_object* v_fn_1434_; lean_object* v_arg_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_fn_1434_ = lean_ctor_get(v_x_1424_, 0);
lean_inc_ref(v_fn_1434_);
v_arg_1435_ = lean_ctor_get(v_x_1424_, 1);
lean_inc_ref(v_arg_1435_);
lean_dec_ref_known(v_x_1424_, 2);
v___x_1436_ = lean_array_set(v_x_1425_, v_x_1426_, v_arg_1435_);
v___x_1437_ = lean_unsigned_to_nat(1u);
v___x_1438_ = lean_nat_sub(v_x_1426_, v___x_1437_);
lean_dec(v_x_1426_);
v_x_1424_ = v_fn_1434_;
v_x_1425_ = v___x_1436_;
v_x_1426_ = v___x_1438_;
goto _start;
}
else
{
lean_object* v___x_1440_; 
lean_dec(v_x_1426_);
v___x_1440_ = l_Lean_Meta_AbstractNestedProofs_visit(v_x_1424_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; size_t v_sz_1442_; size_t v___x_1443_; lean_object* v___x_1444_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v_sz_1442_ = lean_array_size(v_x_1425_);
v___x_1443_ = ((size_t)0ULL);
v___x_1444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_1442_, v___x_1443_, v_x_1425_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1453_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = l_Lean_mkAppN(v_a_1441_, v_a_1445_);
lean_dec(v_a_1445_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1449_);
v___x_1451_ = v___x_1447_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_a_1441_);
v_a_1454_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1444_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1444_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_dec_ref(v_x_1425_);
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object* v_e_1462_, uint8_t v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_a_1471_; lean_object* v___y_1477_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_visit___closed__0));
v___x_1480_ = l_Lean_Core_checkSystem(v___x_1479_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1547_; 
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v___x_1480_, 0);
lean_dec(v_unused_1548_);
v___x_1482_ = v___x_1480_;
v_isShared_1483_ = v_isSharedCheck_1547_;
goto v_resetjp_1481_;
}
else
{
lean_dec(v___x_1480_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1547_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
uint8_t v___x_1484_; 
v___x_1484_ = l_Lean_Expr_isAtomic(v_e_1462_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_st_ref_get(v_a_1464_);
v___x_1486_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v___x_1485_, v_e_1462_);
lean_dec(v___x_1485_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v___x_1487_; 
lean_del_object(v___x_1482_);
lean_inc_ref(v_e_1462_);
v___x_1487_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_1462_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___f_1492_; uint8_t v___x_1493_; uint8_t v___y_1495_; uint8_t v___x_1529_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v___f_1492_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed), 9, 0);
v___x_1493_ = 1;
v___x_1529_ = lean_unbox(v_a_1488_);
if (v___x_1529_ == 0)
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_unbox(v_a_1488_);
lean_dec(v_a_1488_);
v___y_1495_ = v___x_1530_;
goto v___jp_1494_;
}
else
{
uint8_t v___x_1531_; 
lean_dec(v_a_1488_);
v___x_1531_ = l_Lean_Expr_hasSorry(v_e_1462_);
if (v___x_1531_ == 0)
{
lean_dec_ref(v___f_1492_);
goto v___jp_1489_;
}
else
{
if (v___x_1484_ == 0)
{
v___y_1495_ = v___x_1484_;
goto v___jp_1494_;
}
else
{
lean_dec_ref(v___f_1492_);
goto v___jp_1489_;
}
}
}
v___jp_1489_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___boxed), 8, 0);
lean_inc_ref(v_e_1462_);
v___x_1491_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_e_1462_, v_a_1463_, v___x_1490_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
v___y_1477_ = v___x_1491_;
goto v___jp_1476_;
}
v___jp_1494_:
{
switch(lean_obj_tag(v_e_1462_))
{
case 6:
{
lean_object* v___x_1496_; lean_object* v___f_1497_; lean_object* v___x_1498_; 
v___x_1496_ = lean_box(v___y_1495_);
v___f_1497_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1497_, 0, v___x_1496_);
lean_closure_set(v___f_1497_, 1, v___f_1492_);
lean_inc_ref(v_e_1462_);
v___x_1498_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1462_, v___f_1497_, v___y_1495_, v___x_1493_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
v___y_1477_ = v___x_1498_;
goto v___jp_1476_;
}
case 8:
{
lean_object* v___x_1499_; lean_object* v___f_1500_; lean_object* v___x_1501_; 
v___x_1499_ = lean_box(v___y_1495_);
v___f_1500_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1500_, 0, v___x_1499_);
lean_closure_set(v___f_1500_, 1, v___f_1492_);
lean_inc_ref(v_e_1462_);
v___x_1501_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1462_, v___f_1500_, v___y_1495_, v___x_1493_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
v___y_1477_ = v___x_1501_;
goto v___jp_1476_;
}
case 7:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; 
v___x_1502_ = lean_box(v___y_1495_);
v___x_1503_ = lean_box(v___x_1493_);
v___f_1504_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed), 12, 3);
lean_closure_set(v___f_1504_, 0, v___x_1502_);
lean_closure_set(v___f_1504_, 1, v___x_1503_);
lean_closure_set(v___f_1504_, 2, v___f_1492_);
lean_inc_ref(v_e_1462_);
v___x_1505_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_e_1462_, v___f_1504_, v___y_1495_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
v___y_1477_ = v___x_1505_;
goto v___jp_1476_;
}
case 10:
{
lean_object* v_data_1506_; lean_object* v_expr_1507_; lean_object* v___x_1508_; 
lean_dec_ref(v___f_1492_);
v_data_1506_ = lean_ctor_get(v_e_1462_, 0);
v_expr_1507_ = lean_ctor_get(v_e_1462_, 1);
lean_inc_ref(v_expr_1507_);
v___x_1508_ = l_Lean_Meta_AbstractNestedProofs_visit(v_expr_1507_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; size_t v___x_1510_; size_t v___x_1511_; uint8_t v___x_1512_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v___x_1508_, 1);
v___x_1510_ = lean_ptr_addr(v_expr_1507_);
v___x_1511_ = lean_ptr_addr(v_a_1509_);
v___x_1512_ = lean_usize_dec_eq(v___x_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; 
lean_inc(v_data_1506_);
v___x_1513_ = l_Lean_Expr_mdata___override(v_data_1506_, v_a_1509_);
v_a_1471_ = v___x_1513_;
goto v___jp_1470_;
}
else
{
lean_dec(v_a_1509_);
lean_inc_ref(v_e_1462_);
v_a_1471_ = v_e_1462_;
goto v___jp_1470_;
}
}
else
{
v___y_1477_ = v___x_1508_;
goto v___jp_1476_;
}
}
case 11:
{
lean_object* v_typeName_1514_; lean_object* v_idx_1515_; lean_object* v_struct_1516_; lean_object* v___x_1517_; 
lean_dec_ref(v___f_1492_);
v_typeName_1514_ = lean_ctor_get(v_e_1462_, 0);
v_idx_1515_ = lean_ctor_get(v_e_1462_, 1);
v_struct_1516_ = lean_ctor_get(v_e_1462_, 2);
lean_inc_ref(v_struct_1516_);
v___x_1517_ = l_Lean_Meta_AbstractNestedProofs_visit(v_struct_1516_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; size_t v___x_1519_; size_t v___x_1520_; uint8_t v___x_1521_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = lean_ptr_addr(v_struct_1516_);
v___x_1520_ = lean_ptr_addr(v_a_1518_);
v___x_1521_ = lean_usize_dec_eq(v___x_1519_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_inc(v_idx_1515_);
lean_inc(v_typeName_1514_);
v___x_1522_ = l_Lean_Expr_proj___override(v_typeName_1514_, v_idx_1515_, v_a_1518_);
v_a_1471_ = v___x_1522_;
goto v___jp_1470_;
}
else
{
lean_dec(v_a_1518_);
lean_inc_ref(v_e_1462_);
v_a_1471_ = v_e_1462_;
goto v___jp_1470_;
}
}
else
{
v___y_1477_ = v___x_1517_;
goto v___jp_1476_;
}
}
case 5:
{
lean_object* v_dummy_1523_; lean_object* v_nargs_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec_ref(v___f_1492_);
v_dummy_1523_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_1524_ = l_Lean_Expr_getAppNumArgs(v_e_1462_);
lean_inc(v_nargs_1524_);
v___x_1525_ = lean_mk_array(v_nargs_1524_, v_dummy_1523_);
v___x_1526_ = lean_unsigned_to_nat(1u);
v___x_1527_ = lean_nat_sub(v_nargs_1524_, v___x_1526_);
lean_dec(v_nargs_1524_);
lean_inc_ref(v_e_1462_);
v___x_1528_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_e_1462_, v___x_1525_, v___x_1527_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
v___y_1477_ = v___x_1528_;
goto v___jp_1476_;
}
default: 
{
lean_dec_ref(v___f_1492_);
lean_inc_ref(v_e_1462_);
v_a_1471_ = v_e_1462_;
goto v___jp_1470_;
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec_ref(v_e_1462_);
v_a_1532_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1487_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1487_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
else
{
lean_object* v_val_1540_; lean_object* v___x_1542_; 
lean_dec_ref(v_e_1462_);
v_val_1540_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_val_1540_);
lean_dec_ref_known(v___x_1486_, 1);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v_val_1540_);
v___x_1542_ = v___x_1482_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_val_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
else
{
lean_object* v___x_1545_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v_e_1462_);
v___x_1545_ = v___x_1482_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_e_1462_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec_ref(v_e_1462_);
v_a_1549_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1480_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1480_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
v___jp_1470_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1472_ = lean_st_ref_take(v_a_1464_);
lean_inc_ref(v_a_1471_);
v___x_1473_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v___x_1472_, v_e_1462_, v_a_1471_);
v___x_1474_ = lean_st_ref_set(v_a_1464_, v___x_1473_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_a_1471_);
return v___x_1475_;
}
v___jp_1476_:
{
if (lean_obj_tag(v___y_1477_) == 0)
{
lean_object* v_a_1478_; 
v_a_1478_ = lean_ctor_get(v___y_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___y_1477_, 1);
v_a_1471_ = v_a_1478_;
goto v___jp_1470_;
}
else
{
lean_dec_ref(v_e_1462_);
return v___y_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object* v_b_1557_, lean_object* v_xs_1558_, uint8_t v___y_1559_, uint8_t v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1557_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1569_ = 1;
v___x_1570_ = l_Lean_Meta_mkLambdaFVars(v_xs_1558_, v_a_1568_, v___y_1559_, v___y_1559_, v___y_1559_, v___y_1559_, v___x_1569_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1570_;
}
else
{
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object* v_b_1571_, lean_object* v_xs_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
uint8_t v___y_30338__boxed_1581_; uint8_t v___y_30339__boxed_1582_; lean_object* v_res_1583_; 
v___y_30338__boxed_1581_ = lean_unbox(v___y_1573_);
v___y_30339__boxed_1582_ = lean_unbox(v___y_1574_);
v_res_1583_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(v_b_1571_, v_xs_1572_, v___y_30338__boxed_1581_, v___y_30339__boxed_1582_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v_xs_1572_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t v___y_1584_, lean_object* v___f_1585_, lean_object* v_xs_1586_, lean_object* v_b_1587_, uint8_t v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; lean_object* v___f_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1595_ = lean_box(v___y_1584_);
lean_inc_ref(v_xs_1586_);
v___f_1596_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1596_, 0, v_b_1587_);
lean_closure_set(v___f_1596_, 1, v_xs_1586_);
lean_closure_set(v___f_1596_, 2, v___x_1595_);
v___x_1597_ = lean_box(v___y_1588_);
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___y_1589_);
v___x_1598_ = lean_apply_9(v___f_1585_, v_xs_1586_, v___f_1596_, v___x_1597_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, lean_box(0));
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object* v_sz_1599_, lean_object* v_i_1600_, lean_object* v_bs_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
size_t v_sz_boxed_1609_; size_t v_i_boxed_1610_; uint8_t v___y_30378__boxed_1611_; lean_object* v_res_1612_; 
v_sz_boxed_1609_ = lean_unbox_usize(v_sz_1599_);
lean_dec(v_sz_1599_);
v_i_boxed_1610_ = lean_unbox_usize(v_i_1600_);
lean_dec(v_i_1600_);
v___y_30378__boxed_1611_ = lean_unbox(v___y_1602_);
v_res_1612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_boxed_1609_, v_i_boxed_1610_, v_bs_1601_, v___y_30378__boxed_1611_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object* v_x_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
uint8_t v___y_30399__boxed_1623_; lean_object* v_res_1624_; 
v___y_30399__boxed_1623_ = lean_unbox(v___y_1616_);
v_res_1624_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_x_1613_, v_x_1614_, v_x_1615_, v___y_30399__boxed_1623_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object* v_as_1625_, lean_object* v_sz_1626_, lean_object* v_i_1627_, lean_object* v_b_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
size_t v_sz_boxed_1636_; size_t v_i_boxed_1637_; uint8_t v___y_30422__boxed_1638_; lean_object* v_res_1639_; 
v_sz_boxed_1636_ = lean_unbox_usize(v_sz_1626_);
lean_dec(v_sz_1626_);
v_i_boxed_1637_ = lean_unbox_usize(v_i_1627_);
lean_dec(v_i_1627_);
v___y_30422__boxed_1638_ = lean_unbox(v___y_1629_);
v_res_1639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_as_1625_, v_sz_boxed_1636_, v_i_boxed_1637_, v_b_1628_, v___y_30422__boxed_1638_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v_as_1625_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object* v_00_u03b2_1640_, lean_object* v_m_1641_, lean_object* v_a_1642_, lean_object* v_b_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_m_1641_, v_a_1642_, v_b_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object* v_00_u03b2_1645_, lean_object* v_m_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_1646_, v_a_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object* v_00_u03b2_1649_, lean_object* v_m_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_00_u03b2_1649_, v_m_1650_, v_a_1651_);
lean_dec_ref(v_a_1651_);
lean_dec_ref(v_m_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object* v_00_u03b2_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_, lean_object* v_x_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_x_1654_, v_x_1655_, v_x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object* v_00_u03b2_1658_, lean_object* v_a_1659_, lean_object* v_x_1660_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1659_, v_x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1662_, lean_object* v_a_1663_, lean_object* v_x_1664_){
_start:
{
uint8_t v_res_1665_; lean_object* v_r_1666_; 
v_res_1665_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(v_00_u03b2_1662_, v_a_1663_, v_x_1664_);
lean_dec(v_x_1664_);
lean_dec_ref(v_a_1663_);
v_r_1666_ = lean_box(v_res_1665_);
return v_r_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2(lean_object* v_00_u03b2_1667_, lean_object* v_data_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(v_data_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3(lean_object* v_00_u03b2_1670_, lean_object* v_a_1671_, lean_object* v_b_1672_, lean_object* v_x_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1671_, v_b_1672_, v_x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(lean_object* v_00_u03b2_1675_, lean_object* v_a_1676_, lean_object* v_x_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_1676_, v_x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1679_, lean_object* v_a_1680_, lean_object* v_x_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(v_00_u03b2_1679_, v_a_1680_, v_x_1681_);
lean_dec(v_x_1681_);
lean_dec_ref(v_a_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b1_1683_, lean_object* v_x_1684_, uint8_t v_isExporting_1685_, uint8_t v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_1684_, v_isExporting_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___boxed(lean_object* v_00_u03b1_1694_, lean_object* v_x_1695_, lean_object* v_isExporting_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
uint8_t v_isExporting_boxed_1704_; uint8_t v___y_31019__boxed_1705_; lean_object* v_res_1706_; 
v_isExporting_boxed_1704_ = lean_unbox(v_isExporting_1696_);
v___y_31019__boxed_1705_ = lean_unbox(v___y_1697_);
v_res_1706_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(v_00_u03b1_1694_, v_x_1695_, v_isExporting_boxed_1704_, v___y_31019__boxed_1705_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(lean_object* v_00_u03b1_1707_, lean_object* v_x_1708_, uint8_t v_when_1709_, uint8_t v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_1708_, v_when_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1718_, lean_object* v_x_1719_, lean_object* v_when_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
uint8_t v_when_boxed_1728_; uint8_t v___y_31042__boxed_1729_; lean_object* v_res_1730_; 
v_when_boxed_1728_ = lean_unbox(v_when_1720_);
v___y_31042__boxed_1729_ = lean_unbox(v___y_1721_);
v_res_1730_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(v_00_u03b1_1718_, v_x_1719_, v_when_boxed_1728_, v___y_31042__boxed_1729_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9(lean_object* v_00_u03b2_1731_, lean_object* v_x_1732_, size_t v_x_1733_, size_t v_x_1734_, lean_object* v_x_1735_, lean_object* v_x_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_1732_, v_x_1733_, v_x_1734_, v_x_1735_, v_x_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1738_, lean_object* v_x_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_, lean_object* v_x_1742_, lean_object* v_x_1743_){
_start:
{
size_t v_x_31066__boxed_1744_; size_t v_x_31067__boxed_1745_; lean_object* v_res_1746_; 
v_x_31066__boxed_1744_ = lean_unbox_usize(v_x_1740_);
lean_dec(v_x_1740_);
v_x_31067__boxed_1745_ = lean_unbox_usize(v_x_1741_);
lean_dec(v_x_1741_);
v_res_1746_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9(v_00_u03b2_1738_, v_x_1739_, v_x_31066__boxed_1744_, v_x_31067__boxed_1745_, v_x_1742_, v_x_1743_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1747_, lean_object* v_i_1748_, lean_object* v_source_1749_, lean_object* v_target_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(v_i_1748_, v_source_1749_, v_target_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15(lean_object* v_00_u03b2_1752_, lean_object* v_n_1753_, lean_object* v_k_1754_, lean_object* v_v_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(v_n_1753_, v_k_1754_, v_v_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16(lean_object* v_00_u03b2_1757_, size_t v_depth_1758_, lean_object* v_keys_1759_, lean_object* v_vals_1760_, lean_object* v_heq_1761_, lean_object* v_i_1762_, lean_object* v_entries_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_depth_1758_, v_keys_1759_, v_vals_1760_, v_i_1762_, v_entries_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1765_, lean_object* v_depth_1766_, lean_object* v_keys_1767_, lean_object* v_vals_1768_, lean_object* v_heq_1769_, lean_object* v_i_1770_, lean_object* v_entries_1771_){
_start:
{
size_t v_depth_boxed_1772_; lean_object* v_res_1773_; 
v_depth_boxed_1772_ = lean_unbox_usize(v_depth_1766_);
lean_dec(v_depth_1766_);
v_res_1773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16(v_00_u03b2_1765_, v_depth_boxed_1772_, v_keys_1767_, v_vals_1768_, v_heq_1769_, v_i_1770_, v_entries_1771_);
lean_dec_ref(v_vals_1768_);
lean_dec_ref(v_keys_1767_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1774_, lean_object* v_x_1775_, lean_object* v_x_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(v_x_1775_, v_x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19(lean_object* v_00_u03b2_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(v_x_1779_, v_x_1780_, v_x_1781_, v_x_1782_);
return v___x_1783_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__0(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = lean_box(0);
v___x_1785_ = lean_unsigned_to_nat(16u);
v___x_1786_ = lean_mk_array(v___x_1785_, v___x_1784_);
return v___x_1786_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__1(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1787_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__0, &l_Lean_Meta_abstractNestedProofs___closed__0_once, _init_l_Lean_Meta_abstractNestedProofs___closed__0);
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
lean_ctor_set(v___x_1789_, 1, v___x_1787_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs(lean_object* v_e_1790_, uint8_t v_cache_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v___x_1797_; 
lean_inc_ref(v_e_1790_);
v___x_1797_ = l_Lean_Meta_isProof(v_e_1790_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1818_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1818_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1818_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
uint8_t v___x_1802_; 
v___x_1802_ = lean_unbox(v_a_1798_);
lean_dec(v_a_1798_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_del_object(v___x_1800_);
v___x_1803_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__1, &l_Lean_Meta_abstractNestedProofs___closed__1_once, _init_l_Lean_Meta_abstractNestedProofs___closed__1);
v___x_1804_ = lean_st_mk_ref(v___x_1803_);
v___x_1805_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1790_, v_cache_1791_, v___x_1804_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1814_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = lean_st_ref_get(v___x_1804_);
lean_dec(v___x_1804_);
lean_dec(v___x_1810_);
if (v_isShared_1809_ == 0)
{
v___x_1812_ = v___x_1808_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1806_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
else
{
lean_dec(v___x_1804_);
return v___x_1805_;
}
}
else
{
lean_object* v___x_1816_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v_e_1790_);
v___x_1816_ = v___x_1800_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_e_1790_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec_ref(v_e_1790_);
v_a_1819_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1797_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1797_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object* v_e_1827_, lean_object* v_cache_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
uint8_t v_cache_boxed_1834_; lean_object* v_res_1835_; 
v_cache_boxed_1834_ = lean_unbox(v_cache_1828_);
v_res_1835_ = l_Lean_Meta_abstractNestedProofs(v_e_1827_, v_cache_boxed_1834_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
return v_res_1835_;
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
