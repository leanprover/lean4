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
lean_object* l_Lean_Environment_header(lean_object*);
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
v___x_327_ = lean_st_ref_set(v___y_305_, v___x_326_);
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
v___x_339_ = lean_st_ref_set(v___y_303_, v___x_338_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(lean_object* v_x_490_, uint8_t v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_box(v___y_491_);
lean_inc(v___y_492_);
v___x_499_ = lean_apply_7(v_x_490_, v___x_498_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, lean_box(0));
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed(lean_object* v_x_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v___y_29346__boxed_508_; lean_object* v_res_509_; 
v___y_29346__boxed_508_ = lean_unbox(v___y_501_);
v_res_509_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(v_x_500_, v___y_29346__boxed_508_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_502_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(lean_object* v_lctx_510_, lean_object* v_localInsts_511_, lean_object* v_x_512_, uint8_t v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; lean_object* v___f_521_; lean_object* v___x_522_; 
v___x_520_ = lean_box(v___y_513_);
lean_inc(v___y_514_);
v___f_521_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed), 8, 3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___boxed(lean_object* v_lctx_531_, lean_object* v_localInsts_532_, lean_object* v_x_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint8_t v___y_29371__boxed_541_; lean_object* v_res_542_; 
v___y_29371__boxed_541_ = lean_unbox(v___y_534_);
v_res_542_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_lctx_531_, v_localInsts_532_, v_x_533_, v___y_29371__boxed_541_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object* v_00_u03b1_543_, lean_object* v_lctx_544_, lean_object* v_localInsts_545_, lean_object* v_x_546_, uint8_t v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_lctx_544_, v_localInsts_545_, v_x_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object* v_00_u03b1_555_, lean_object* v_lctx_556_, lean_object* v_localInsts_557_, lean_object* v_x_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
uint8_t v___y_29415__boxed_566_; lean_object* v_res_567_; 
v___y_29415__boxed_566_ = lean_unbox(v___y_559_);
v_res_567_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_00_u03b1_555_, v_lctx_556_, v_localInsts_557_, v_x_558_, v___y_29415__boxed_566_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(lean_object* v_k_568_, uint8_t v___y_569_, lean_object* v___y_570_, lean_object* v_b_571_, lean_object* v_c_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed(lean_object* v_k_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v_b_583_, lean_object* v_c_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
uint8_t v___y_29438__boxed_590_; lean_object* v_res_591_; 
v___y_29438__boxed_590_ = lean_unbox(v___y_581_);
v_res_591_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(v_k_580_, v___y_29438__boxed_590_, v___y_582_, v_b_583_, v_c_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_582_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object* v_e_592_, lean_object* v_k_593_, uint8_t v_cleanupAnnotations_594_, uint8_t v_preserveNondepLet_595_, uint8_t v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; lean_object* v___f_604_; uint8_t v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_603_ = lean_box(v___y_596_);
lean_inc(v___y_597_);
v___f_604_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 10, 3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object* v_e_617_, lean_object* v_k_618_, lean_object* v_cleanupAnnotations_619_, lean_object* v_preserveNondepLet_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_628_; uint8_t v_preserveNondepLet_boxed_629_; uint8_t v___y_29463__boxed_630_; lean_object* v_res_631_; 
v_cleanupAnnotations_boxed_628_ = lean_unbox(v_cleanupAnnotations_619_);
v_preserveNondepLet_boxed_629_ = lean_unbox(v_preserveNondepLet_620_);
v___y_29463__boxed_630_ = lean_unbox(v___y_621_);
v_res_631_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_617_, v_k_618_, v_cleanupAnnotations_boxed_628_, v_preserveNondepLet_boxed_629_, v___y_29463__boxed_630_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object* v_00_u03b1_632_, lean_object* v_e_633_, lean_object* v_k_634_, uint8_t v_cleanupAnnotations_635_, uint8_t v_preserveNondepLet_636_, uint8_t v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_633_, v_k_634_, v_cleanupAnnotations_635_, v_preserveNondepLet_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object* v_00_u03b1_645_, lean_object* v_e_646_, lean_object* v_k_647_, lean_object* v_cleanupAnnotations_648_, lean_object* v_preserveNondepLet_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_657_; uint8_t v_preserveNondepLet_boxed_658_; uint8_t v___y_29513__boxed_659_; lean_object* v_res_660_; 
v_cleanupAnnotations_boxed_657_ = lean_unbox(v_cleanupAnnotations_648_);
v_preserveNondepLet_boxed_658_ = lean_unbox(v_preserveNondepLet_649_);
v___y_29513__boxed_659_ = lean_unbox(v___y_650_);
v_res_660_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(v_00_u03b1_645_, v_e_646_, v_k_647_, v_cleanupAnnotations_boxed_657_, v_preserveNondepLet_boxed_658_, v___y_29513__boxed_659_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(lean_object* v_type_661_, lean_object* v_k_662_, uint8_t v_cleanupAnnotations_663_, uint8_t v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; lean_object* v___f_672_; uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_671_ = lean_box(v___y_664_);
lean_inc(v___y_665_);
v___f_672_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 10, 3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___boxed(lean_object* v_type_684_, lean_object* v_k_685_, lean_object* v_cleanupAnnotations_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_694_; uint8_t v___y_29536__boxed_695_; lean_object* v_res_696_; 
v_cleanupAnnotations_boxed_694_ = lean_unbox(v_cleanupAnnotations_686_);
v___y_29536__boxed_695_ = lean_unbox(v___y_687_);
v_res_696_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_684_, v_k_685_, v_cleanupAnnotations_boxed_694_, v___y_29536__boxed_695_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object* v_00_u03b1_697_, lean_object* v_type_698_, lean_object* v_k_699_, uint8_t v_cleanupAnnotations_700_, uint8_t v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_698_, v_k_699_, v_cleanupAnnotations_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object* v_00_u03b1_709_, lean_object* v_type_710_, lean_object* v_k_711_, lean_object* v_cleanupAnnotations_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_720_; uint8_t v___y_29584__boxed_721_; lean_object* v_res_722_; 
v_cleanupAnnotations_boxed_720_ = lean_unbox(v_cleanupAnnotations_712_);
v___y_29584__boxed_721_ = lean_unbox(v___y_713_);
v_res_722_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_00_u03b1_709_, v_type_710_, v_k_711_, v_cleanupAnnotations_boxed_720_, v___y_29584__boxed_721_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
lean_object* v_ks_727_; lean_object* v_vs_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_752_; 
v_ks_727_ = lean_ctor_get(v_x_723_, 0);
v_vs_728_ = lean_ctor_get(v_x_723_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v_x_723_);
if (v_isSharedCheck_752_ == 0)
{
v___x_730_ = v_x_723_;
v_isShared_731_ = v_isSharedCheck_752_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_vs_728_);
lean_inc(v_ks_727_);
lean_dec(v_x_723_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_752_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_array_get_size(v_ks_727_);
v___x_733_ = lean_nat_dec_lt(v_x_724_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
lean_dec(v_x_724_);
v___x_734_ = lean_array_push(v_ks_727_, v_x_725_);
v___x_735_ = lean_array_push(v_vs_728_, v_x_726_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_735_);
lean_ctor_set(v___x_730_, 0, v___x_734_);
v___x_737_ = v___x_730_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v_k_x27_739_; uint8_t v___x_740_; 
v_k_x27_739_ = lean_array_fget_borrowed(v_ks_727_, v_x_724_);
v___x_740_ = l_Lean_instBEqFVarId_beq(v_x_725_, v_k_x27_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_742_; 
if (v_isShared_731_ == 0)
{
v___x_742_ = v___x_730_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_ks_727_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_vs_728_);
v___x_742_ = v_reuseFailAlloc_746_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_nat_add(v_x_724_, v___x_743_);
lean_dec(v_x_724_);
v_x_723_ = v___x_742_;
v_x_724_ = v___x_744_;
goto _start;
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_747_ = lean_array_fset(v_ks_727_, v_x_724_, v_x_725_);
v___x_748_ = lean_array_fset(v_vs_728_, v_x_724_, v_x_726_);
lean_dec(v_x_724_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_748_);
lean_ctor_set(v___x_730_, 0, v___x_747_);
v___x_750_ = v___x_730_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(lean_object* v_n_753_, lean_object* v_k_754_, lean_object* v_v_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(v_n_753_, v___x_756_, v_k_754_, v_v_755_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0(void){
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
lean_object* v_es_764_; size_t v___x_765_; size_t v___x_766_; lean_object* v_j_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v_es_764_ = lean_ctor_get(v_x_759_, 0);
v___x_765_ = ((size_t)31ULL);
v___x_766_ = lean_usize_land(v_x_760_, v___x_765_);
v_j_767_ = lean_usize_to_nat(v___x_766_);
v___x_768_ = lean_array_get_size(v_es_764_);
v___x_769_ = lean_nat_dec_lt(v_j_767_, v___x_768_);
if (v___x_769_ == 0)
{
lean_dec(v_j_767_);
lean_dec(v_x_763_);
lean_dec(v_x_762_);
return v_x_759_;
}
else
{
lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_808_; 
lean_inc_ref(v_es_764_);
v_isSharedCheck_808_ = !lean_is_exclusive(v_x_759_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v_x_759_, 0);
lean_dec(v_unused_809_);
v___x_771_ = v_x_759_;
v_isShared_772_ = v_isSharedCheck_808_;
goto v_resetjp_770_;
}
else
{
lean_dec(v_x_759_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_808_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_v_773_; lean_object* v___x_774_; lean_object* v_xs_x27_775_; lean_object* v___y_777_; 
v_v_773_ = lean_array_fget(v_es_764_, v_j_767_);
v___x_774_ = lean_box(0);
v_xs_x27_775_ = lean_array_fset(v_es_764_, v_j_767_, v___x_774_);
switch(lean_obj_tag(v_v_773_))
{
case 0:
{
lean_object* v_key_782_; lean_object* v_val_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_793_; 
v_key_782_ = lean_ctor_get(v_v_773_, 0);
v_val_783_ = lean_ctor_get(v_v_773_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_v_773_);
if (v_isSharedCheck_793_ == 0)
{
v___x_785_ = v_v_773_;
v_isShared_786_ = v_isSharedCheck_793_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_val_783_);
lean_inc(v_key_782_);
lean_dec(v_v_773_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_793_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
uint8_t v___x_787_; 
v___x_787_ = l_Lean_instBEqFVarId_beq(v_x_762_, v_key_782_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
lean_del_object(v___x_785_);
v___x_788_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_782_, v_val_783_, v_x_762_, v_x_763_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
v___y_777_ = v___x_789_;
goto v___jp_776_;
}
else
{
lean_object* v___x_791_; 
lean_dec(v_val_783_);
lean_dec(v_key_782_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v_x_763_);
lean_ctor_set(v___x_785_, 0, v_x_762_);
v___x_791_ = v___x_785_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_x_762_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_x_763_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
v___y_777_ = v___x_791_;
goto v___jp_776_;
}
}
}
}
case 1:
{
lean_object* v_node_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_806_; 
v_node_794_ = lean_ctor_get(v_v_773_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_v_773_);
if (v_isSharedCheck_806_ == 0)
{
v___x_796_ = v_v_773_;
v_isShared_797_ = v_isSharedCheck_806_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_node_794_);
lean_dec(v_v_773_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_806_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_798_ = ((size_t)5ULL);
v___x_799_ = lean_usize_shift_right(v_x_760_, v___x_798_);
v___x_800_ = ((size_t)1ULL);
v___x_801_ = lean_usize_add(v_x_761_, v___x_800_);
v___x_802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_node_794_, v___x_799_, v___x_801_, v_x_762_, v_x_763_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_802_);
v___x_804_ = v___x_796_;
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
v___y_777_ = v___x_804_;
goto v___jp_776_;
}
}
}
default: 
{
lean_object* v___x_807_; 
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_x_762_);
lean_ctor_set(v___x_807_, 1, v_x_763_);
v___y_777_ = v___x_807_;
goto v___jp_776_;
}
}
v___jp_776_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_array_fset(v_xs_x27_775_, v_j_767_, v___y_777_);
lean_dec(v_j_767_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_778_);
v___x_780_ = v___x_771_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
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
v___x_823_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg___closed__0);
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
size_t v_x_29684__boxed_864_; size_t v_x_29685__boxed_865_; lean_object* v_res_866_; 
v_x_29684__boxed_864_ = lean_unbox_usize(v_x_860_);
lean_dec(v_x_860_);
v_x_29685__boxed_865_ = lean_unbox_usize(v_x_861_);
lean_dec(v_x_861_);
v_res_866_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_859_, v_x_29684__boxed_864_, v_x_29685__boxed_865_, v_x_862_, v_x_863_);
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
lean_object* v___x_916_; lean_object* v_env_917_; uint8_t v_isExporting_918_; lean_object* v___x_985_; uint8_t v_isModule_986_; 
v___x_916_ = lean_st_ref_get(v___y_914_);
v_env_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc_ref(v_env_917_);
lean_dec(v___x_916_);
v_isExporting_918_ = lean_ctor_get_uint8(v_env_917_, sizeof(void*)*8);
v___x_985_ = l_Lean_Environment_header(v_env_917_);
lean_dec_ref(v_env_917_);
v_isModule_986_ = lean_ctor_get_uint8(v___x_985_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_985_);
if (v_isModule_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_box(v___y_909_);
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
v___x_988_ = lean_apply_7(v_x_907_, v___x_987_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, lean_box(0));
return v___x_988_;
}
else
{
if (v_isExporting_918_ == 0)
{
if (v_isExporting_908_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_box(v___y_909_);
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
v___x_990_ = lean_apply_7(v_x_907_, v___x_989_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, lean_box(0));
return v___x_990_;
}
else
{
goto v___jp_919_;
}
}
else
{
if (v_isExporting_908_ == 0)
{
goto v___jp_919_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_box(v___y_909_);
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
v___x_992_ = lean_apply_7(v_x_907_, v___x_991_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, lean_box(0));
return v___x_992_;
}
}
}
v___jp_919_:
{
lean_object* v___x_920_; lean_object* v_env_921_; lean_object* v_nextMacroScope_922_; lean_object* v_ngen_923_; lean_object* v_auxDeclNGen_924_; lean_object* v_traceState_925_; lean_object* v_messages_926_; lean_object* v_infoState_927_; lean_object* v_snapshotTasks_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_983_; 
v___x_920_ = lean_st_ref_take(v___y_914_);
v_env_921_ = lean_ctor_get(v___x_920_, 0);
v_nextMacroScope_922_ = lean_ctor_get(v___x_920_, 1);
v_ngen_923_ = lean_ctor_get(v___x_920_, 2);
v_auxDeclNGen_924_ = lean_ctor_get(v___x_920_, 3);
v_traceState_925_ = lean_ctor_get(v___x_920_, 4);
v_messages_926_ = lean_ctor_get(v___x_920_, 6);
v_infoState_927_ = lean_ctor_get(v___x_920_, 7);
v_snapshotTasks_928_ = lean_ctor_get(v___x_920_, 8);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v___x_920_, 5);
lean_dec(v_unused_984_);
v___x_930_ = v___x_920_;
v_isShared_931_ = v_isSharedCheck_983_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_snapshotTasks_928_);
lean_inc(v_infoState_927_);
lean_inc(v_messages_926_);
lean_inc(v_traceState_925_);
lean_inc(v_auxDeclNGen_924_);
lean_inc(v_ngen_923_);
lean_inc(v_nextMacroScope_922_);
lean_inc(v_env_921_);
lean_dec(v___x_920_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_983_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_932_ = l_Lean_Environment_setExporting(v_env_921_, v_isExporting_908_);
v___x_933_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 5, v___x_933_);
lean_ctor_set(v___x_930_, 0, v___x_932_);
v___x_935_ = v___x_930_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_nextMacroScope_922_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_ngen_923_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v_auxDeclNGen_924_);
lean_ctor_set(v_reuseFailAlloc_982_, 4, v_traceState_925_);
lean_ctor_set(v_reuseFailAlloc_982_, 5, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_982_, 6, v_messages_926_);
lean_ctor_set(v_reuseFailAlloc_982_, 7, v_infoState_927_);
lean_ctor_set(v_reuseFailAlloc_982_, 8, v_snapshotTasks_928_);
v___x_935_ = v_reuseFailAlloc_982_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v_mctx_938_; lean_object* v_zetaDeltaFVarIds_939_; lean_object* v_postponed_940_; lean_object* v_diag_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_980_; 
v___x_936_ = lean_st_ref_set(v___y_914_, v___x_935_);
v___x_937_ = lean_st_ref_take(v___y_912_);
v_mctx_938_ = lean_ctor_get(v___x_937_, 0);
v_zetaDeltaFVarIds_939_ = lean_ctor_get(v___x_937_, 2);
v_postponed_940_ = lean_ctor_get(v___x_937_, 3);
v_diag_941_ = lean_ctor_get(v___x_937_, 4);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v___x_937_, 1);
lean_dec(v_unused_981_);
v___x_943_ = v___x_937_;
v_isShared_944_ = v_isSharedCheck_980_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_diag_941_);
lean_inc(v_postponed_940_);
lean_inc(v_zetaDeltaFVarIds_939_);
lean_inc(v_mctx_938_);
lean_dec(v___x_937_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_980_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_945_);
v___x_947_ = v___x_943_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_mctx_938_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_zetaDeltaFVarIds_939_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_postponed_940_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_diag_941_);
v___x_947_ = v_reuseFailAlloc_979_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_r_950_; 
v___x_948_ = lean_st_ref_set(v___y_912_, v___x_947_);
v___x_949_ = lean_box(v___y_909_);
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
v_r_950_ = lean_apply_7(v_x_907_, v___x_949_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, lean_box(0));
if (lean_obj_tag(v_r_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_967_; 
v_a_951_ = lean_ctor_get(v_r_950_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v_r_950_);
if (v_isSharedCheck_967_ == 0)
{
v___x_953_ = v_r_950_;
v_isShared_954_ = v_isSharedCheck_967_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v_r_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_967_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
lean_inc(v_a_951_);
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 1);
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_966_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v___x_957_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_914_, v_isExporting_918_, v___x_933_, v___y_912_, v___x_945_, v___x_956_);
lean_dec_ref(v___x_956_);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v___x_957_, 0);
lean_dec(v_unused_965_);
v___x_959_ = v___x_957_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_dec(v___x_957_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v_a_951_);
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_951_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_a_968_ = lean_ctor_get(v_r_950_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v_r_950_, 1);
v___x_969_ = lean_box(0);
v___x_970_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_914_, v_isExporting_918_, v___x_933_, v___y_912_, v___x_945_, v___x_969_);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v___x_970_, 0);
lean_dec(v_unused_978_);
v___x_972_ = v___x_970_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_dec(v___x_970_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 1);
lean_ctor_set(v___x_972_, 0, v_a_968_);
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_968_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg___boxed(lean_object* v_x_993_, lean_object* v_isExporting_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v_isExporting_boxed_1002_; uint8_t v___y_29914__boxed_1003_; lean_object* v_res_1004_; 
v_isExporting_boxed_1002_ = lean_unbox(v_isExporting_994_);
v___y_29914__boxed_1003_ = lean_unbox(v___y_995_);
v_res_1004_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_993_, v_isExporting_boxed_1002_, v___y_29914__boxed_1003_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(lean_object* v_x_1005_, uint8_t v_when_1006_, uint8_t v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
if (v_when_1006_ == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_box(v___y_1007_);
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
lean_inc(v___y_1008_);
v___x_1015_ = lean_apply_7(v_x_1005_, v___x_1014_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, lean_box(0));
return v___x_1015_;
}
else
{
uint8_t v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = 0;
v___x_1017_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_1005_, v___x_1016_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___boxed(lean_object* v_x_1018_, lean_object* v_when_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
uint8_t v_when_boxed_1027_; uint8_t v___y_30063__boxed_1028_; lean_object* v_res_1029_; 
v_when_boxed_1027_ = lean_unbox(v_when_1019_);
v___y_30063__boxed_1028_ = lean_unbox(v___y_1020_);
v_res_1029_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_1018_, v_when_boxed_1027_, v___y_30063__boxed_1028_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0(lean_object* v_proof_1030_, uint8_t v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; 
lean_inc(v___y_1036_);
lean_inc_ref(v___y_1035_);
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
v___x_1038_ = lean_infer_type(v_proof_1030_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0___boxed(lean_object* v_proof_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v___y_30092__boxed_1047_; lean_object* v_res_1048_; 
v___y_30092__boxed_1047_ = lean_unbox(v___y_1040_);
v_res_1048_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0(v_proof_1039_, v___y_30092__boxed_1047_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object* v_proof_1049_, uint8_t v_cache_1050_, lean_object* v_postprocessType_1051_, uint8_t v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___f_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; 
lean_inc_ref(v_proof_1049_);
v___f_1059_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1059_, 0, v_proof_1049_);
v___x_1060_ = 1;
v___x_1061_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v___f_1059_, v___x_1060_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1063_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1061_, 1);
v___x_1063_ = l_Lean_Core_betaReduce(v_a_1062_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1065_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1065_ = l_Lean_Meta_zetaReduce(v_a_1064_, v___x_1060_, v___x_1060_, v___x_1060_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v___x_1067_ = lean_box(v___y_1052_);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
v___x_1068_ = lean_apply_8(v_postprocessType_1051_, v_a_1066_, v___x_1067_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, lean_box(0));
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; uint8_t v___y_1071_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
if (v_cache_1050_ == 0)
{
v___y_1071_ = v_cache_1050_;
goto v___jp_1070_;
}
else
{
uint8_t v___x_1074_; 
v___x_1074_ = l_Lean_Expr_hasSorry(v_proof_1049_);
if (v___x_1074_ == 0)
{
v___y_1071_ = v_cache_1050_;
goto v___jp_1070_;
}
else
{
uint8_t v___x_1075_; 
v___x_1075_ = 0;
v___y_1071_ = v___x_1075_;
goto v___jp_1070_;
}
}
v___jp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_box(0);
v___x_1073_ = l_Lean_Meta_mkAuxTheorem(v_a_1069_, v_proof_1049_, v___x_1060_, v___x_1072_, v___y_1071_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
return v___x_1073_;
}
}
else
{
lean_dec_ref(v_proof_1049_);
return v___x_1068_;
}
}
else
{
lean_dec_ref(v_postprocessType_1051_);
lean_dec_ref(v_proof_1049_);
return v___x_1065_;
}
}
else
{
lean_dec_ref(v_postprocessType_1051_);
lean_dec_ref(v_proof_1049_);
return v___x_1063_;
}
}
else
{
lean_dec_ref(v_postprocessType_1051_);
lean_dec_ref(v_proof_1049_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object* v_proof_1076_, lean_object* v_cache_1077_, lean_object* v_postprocessType_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
uint8_t v_cache_boxed_1086_; uint8_t v___y_30115__boxed_1087_; lean_object* v_res_1088_; 
v_cache_boxed_1086_ = lean_unbox(v_cache_1077_);
v___y_30115__boxed_1087_ = lean_unbox(v___y_1079_);
v_res_1088_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_proof_1076_, v_cache_boxed_1086_, v_postprocessType_1078_, v___y_30115__boxed_1087_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
if (lean_obj_tag(v_x_1090_) == 0)
{
return v_x_1089_;
}
else
{
lean_object* v_key_1091_; lean_object* v_value_1092_; lean_object* v_tail_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1116_; 
v_key_1091_ = lean_ctor_get(v_x_1090_, 0);
v_value_1092_ = lean_ctor_get(v_x_1090_, 1);
v_tail_1093_ = lean_ctor_get(v_x_1090_, 2);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_x_1090_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1095_ = v_x_1090_;
v_isShared_1096_ = v_isSharedCheck_1116_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_tail_1093_);
lean_inc(v_value_1092_);
lean_inc(v_key_1091_);
lean_dec(v_x_1090_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1116_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; uint64_t v_fold_1101_; uint64_t v___x_1102_; uint64_t v___x_1103_; uint64_t v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1097_ = lean_array_get_size(v_x_1089_);
v___x_1098_ = l_Lean_ExprStructEq_hash(v_key_1091_);
v___x_1099_ = 32ULL;
v___x_1100_ = lean_uint64_shift_right(v___x_1098_, v___x_1099_);
v_fold_1101_ = lean_uint64_xor(v___x_1098_, v___x_1100_);
v___x_1102_ = 16ULL;
v___x_1103_ = lean_uint64_shift_right(v_fold_1101_, v___x_1102_);
v___x_1104_ = lean_uint64_xor(v_fold_1101_, v___x_1103_);
v___x_1105_ = lean_uint64_to_usize(v___x_1104_);
v___x_1106_ = lean_usize_of_nat(v___x_1097_);
v___x_1107_ = ((size_t)1ULL);
v___x_1108_ = lean_usize_sub(v___x_1106_, v___x_1107_);
v___x_1109_ = lean_usize_land(v___x_1105_, v___x_1108_);
v___x_1110_ = lean_array_uget_borrowed(v_x_1089_, v___x_1109_);
lean_inc(v___x_1110_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 2, v___x_1110_);
v___x_1112_ = v___x_1095_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_key_1091_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_value_1092_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_array_uset(v_x_1089_, v___x_1109_, v___x_1112_);
v_x_1089_ = v___x_1113_;
v_x_1090_ = v_tail_1093_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(lean_object* v_i_1117_, lean_object* v_source_1118_, lean_object* v_target_1119_){
_start:
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = lean_array_get_size(v_source_1118_);
v___x_1121_ = lean_nat_dec_lt(v_i_1117_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_dec_ref(v_source_1118_);
lean_dec(v_i_1117_);
return v_target_1119_;
}
else
{
lean_object* v_es_1122_; lean_object* v___x_1123_; lean_object* v_source_1124_; lean_object* v_target_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v_es_1122_ = lean_array_fget(v_source_1118_, v_i_1117_);
v___x_1123_ = lean_box(0);
v_source_1124_ = lean_array_fset(v_source_1118_, v_i_1117_, v___x_1123_);
v_target_1125_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(v_target_1119_, v_es_1122_);
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_add(v_i_1117_, v___x_1126_);
lean_dec(v_i_1117_);
v_i_1117_ = v___x_1127_;
v_source_1118_ = v_source_1124_;
v_target_1119_ = v_target_1125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(lean_object* v_data_1129_){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v_nbuckets_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1130_ = lean_array_get_size(v_data_1129_);
v___x_1131_ = lean_unsigned_to_nat(2u);
v_nbuckets_1132_ = lean_nat_mul(v___x_1130_, v___x_1131_);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_mk_array(v_nbuckets_1132_, v___x_1134_);
v___x_1136_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(v___x_1133_, v_data_1129_, v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object* v_a_1137_, lean_object* v_x_1138_){
_start:
{
if (lean_obj_tag(v_x_1138_) == 0)
{
uint8_t v___x_1139_; 
v___x_1139_ = 0;
return v___x_1139_;
}
else
{
lean_object* v_key_1140_; lean_object* v_tail_1141_; uint8_t v___x_1142_; 
v_key_1140_ = lean_ctor_get(v_x_1138_, 0);
v_tail_1141_ = lean_ctor_get(v_x_1138_, 2);
v___x_1142_ = l_Lean_ExprStructEq_beq(v_key_1140_, v_a_1137_);
if (v___x_1142_ == 0)
{
v_x_1138_ = v_tail_1141_;
goto _start;
}
else
{
return v___x_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_1144_, lean_object* v_x_1145_){
_start:
{
uint8_t v_res_1146_; lean_object* v_r_1147_; 
v_res_1146_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1144_, v_x_1145_);
lean_dec(v_x_1145_);
lean_dec_ref(v_a_1144_);
v_r_1147_ = lean_box(v_res_1146_);
return v_r_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(lean_object* v_a_1148_, lean_object* v_b_1149_, lean_object* v_x_1150_){
_start:
{
if (lean_obj_tag(v_x_1150_) == 0)
{
lean_dec(v_b_1149_);
lean_dec_ref(v_a_1148_);
return v_x_1150_;
}
else
{
lean_object* v_key_1151_; lean_object* v_value_1152_; lean_object* v_tail_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1165_; 
v_key_1151_ = lean_ctor_get(v_x_1150_, 0);
v_value_1152_ = lean_ctor_get(v_x_1150_, 1);
v_tail_1153_ = lean_ctor_get(v_x_1150_, 2);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1155_ = v_x_1150_;
v_isShared_1156_ = v_isSharedCheck_1165_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_tail_1153_);
lean_inc(v_value_1152_);
lean_inc(v_key_1151_);
lean_dec(v_x_1150_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1165_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
uint8_t v___x_1157_; 
v___x_1157_ = l_Lean_ExprStructEq_beq(v_key_1151_, v_a_1148_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1148_, v_b_1149_, v_tail_1153_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 2, v___x_1158_);
v___x_1160_ = v___x_1155_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_key_1151_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_value_1152_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
else
{
lean_object* v___x_1163_; 
lean_dec(v_value_1152_);
lean_dec(v_key_1151_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 1, v_b_1149_);
lean_ctor_set(v___x_1155_, 0, v_a_1148_);
v___x_1163_ = v___x_1155_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1148_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_b_1149_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_tail_1153_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object* v_m_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_){
_start:
{
lean_object* v_size_1169_; lean_object* v_buckets_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1213_; 
v_size_1169_ = lean_ctor_get(v_m_1166_, 0);
v_buckets_1170_ = lean_ctor_get(v_m_1166_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_m_1166_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1172_ = v_m_1166_;
v_isShared_1173_ = v_isSharedCheck_1213_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_buckets_1170_);
lean_inc(v_size_1169_);
lean_dec(v_m_1166_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1213_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; uint64_t v___x_1175_; uint64_t v___x_1176_; uint64_t v___x_1177_; uint64_t v_fold_1178_; uint64_t v___x_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; size_t v___x_1185_; size_t v___x_1186_; lean_object* v_bkt_1187_; uint8_t v___x_1188_; 
v___x_1174_ = lean_array_get_size(v_buckets_1170_);
v___x_1175_ = l_Lean_ExprStructEq_hash(v_a_1167_);
v___x_1176_ = 32ULL;
v___x_1177_ = lean_uint64_shift_right(v___x_1175_, v___x_1176_);
v_fold_1178_ = lean_uint64_xor(v___x_1175_, v___x_1177_);
v___x_1179_ = 16ULL;
v___x_1180_ = lean_uint64_shift_right(v_fold_1178_, v___x_1179_);
v___x_1181_ = lean_uint64_xor(v_fold_1178_, v___x_1180_);
v___x_1182_ = lean_uint64_to_usize(v___x_1181_);
v___x_1183_ = lean_usize_of_nat(v___x_1174_);
v___x_1184_ = ((size_t)1ULL);
v___x_1185_ = lean_usize_sub(v___x_1183_, v___x_1184_);
v___x_1186_ = lean_usize_land(v___x_1182_, v___x_1185_);
v_bkt_1187_ = lean_array_uget_borrowed(v_buckets_1170_, v___x_1186_);
v___x_1188_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1167_, v_bkt_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v_size_x27_1190_; lean_object* v___x_1191_; lean_object* v_buckets_x27_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1189_ = lean_unsigned_to_nat(1u);
v_size_x27_1190_ = lean_nat_add(v_size_1169_, v___x_1189_);
lean_dec(v_size_1169_);
lean_inc(v_bkt_1187_);
v___x_1191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1191_, 0, v_a_1167_);
lean_ctor_set(v___x_1191_, 1, v_b_1168_);
lean_ctor_set(v___x_1191_, 2, v_bkt_1187_);
v_buckets_x27_1192_ = lean_array_uset(v_buckets_1170_, v___x_1186_, v___x_1191_);
v___x_1193_ = lean_unsigned_to_nat(4u);
v___x_1194_ = lean_nat_mul(v_size_x27_1190_, v___x_1193_);
v___x_1195_ = lean_unsigned_to_nat(3u);
v___x_1196_ = lean_nat_div(v___x_1194_, v___x_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_array_get_size(v_buckets_x27_1192_);
v___x_1198_ = lean_nat_dec_le(v___x_1196_, v___x_1197_);
lean_dec(v___x_1196_);
if (v___x_1198_ == 0)
{
lean_object* v_val_1199_; lean_object* v___x_1201_; 
v_val_1199_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(v_buckets_x27_1192_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_val_1199_);
lean_ctor_set(v___x_1172_, 0, v_size_x27_1190_);
v___x_1201_ = v___x_1172_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_size_x27_1190_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_val_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
else
{
lean_object* v___x_1204_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_buckets_x27_1192_);
lean_ctor_set(v___x_1172_, 0, v_size_x27_1190_);
v___x_1204_ = v___x_1172_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_size_x27_1190_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_buckets_x27_1192_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_object* v___x_1206_; lean_object* v_buckets_x27_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
lean_inc(v_bkt_1187_);
v___x_1206_ = lean_box(0);
v_buckets_x27_1207_ = lean_array_uset(v_buckets_1170_, v___x_1186_, v___x_1206_);
v___x_1208_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1167_, v_b_1168_, v_bkt_1187_);
v___x_1209_ = lean_array_uset(v_buckets_x27_1207_, v___x_1186_, v___x_1208_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v___x_1209_);
v___x_1211_ = v___x_1172_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_size_1169_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object* v_e_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
uint8_t v_a_boxed_1223_; lean_object* v_res_1224_; 
v_a_boxed_1223_ = lean_unbox(v_a_1216_);
v_res_1224_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1215_, v_a_boxed_1223_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object* v_as_1225_, size_t v_sz_1226_, size_t v_i_1227_, lean_object* v_b_1228_, uint8_t v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_a_1237_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; uint8_t v___x_1250_; 
v___x_1250_ = lean_usize_dec_lt(v_i_1227_, v_sz_1226_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v_b_1228_);
return v___x_1251_;
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1253_; lean_object* v_localDecl_1255_; lean_object* v___x_1263_; 
v_a_1252_ = lean_array_uget_borrowed(v_as_1225_, v_i_1227_);
v___x_1253_ = l_Lean_Expr_fvarId_x21(v_a_1252_);
lean_inc(v___x_1253_);
v___x_1263_ = l_Lean_FVarId_getDecl___redArg(v___x_1253_, v___y_1231_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = l_Lean_LocalDecl_type(v_a_1264_);
v___x_1266_ = l_Lean_Meta_AbstractNestedProofs_visit(v___x_1265_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1268_ = l_Lean_LocalDecl_setType(v_a_1264_, v_a_1267_);
v___x_1269_ = l_Lean_LocalDecl_value_x3f(v___x_1268_, v___x_1250_);
if (lean_obj_tag(v___x_1269_) == 0)
{
v_localDecl_1255_ = v___x_1268_;
goto v___jp_1254_;
}
else
{
lean_object* v_val_1270_; lean_object* v___x_1271_; 
v_val_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = l_Lean_Meta_AbstractNestedProofs_visit(v_val_1270_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1273_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v___x_1273_ = l_Lean_LocalDecl_setValue(v___x_1268_, v_a_1272_);
v_localDecl_1255_ = v___x_1273_;
goto v___jp_1254_;
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v___x_1268_);
lean_dec(v___x_1253_);
lean_dec_ref(v_b_1228_);
v_a_1274_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1271_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1271_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_a_1264_);
lean_dec(v___x_1253_);
lean_dec_ref(v_b_1228_);
v_a_1282_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1266_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1266_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v___x_1253_);
lean_dec_ref(v_b_1228_);
v_a_1290_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1263_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1263_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
v___jp_1254_:
{
lean_object* v_fvarIdToDecl_1256_; lean_object* v_decls_1257_; lean_object* v_auxDeclToFullName_1258_; lean_object* v___x_1259_; 
v_fvarIdToDecl_1256_ = lean_ctor_get(v_b_1228_, 0);
v_decls_1257_ = lean_ctor_get(v_b_1228_, 1);
v_auxDeclToFullName_1258_ = lean_ctor_get(v_b_1228_, 2);
lean_inc_ref(v_b_1228_);
v___x_1259_ = lean_local_ctx_find(v_b_1228_, v___x_1253_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_dec_ref(v_localDecl_1255_);
v_a_1237_ = v_b_1228_;
goto v___jp_1236_;
}
else
{
lean_object* v_index_1260_; lean_object* v_fvarId_1261_; lean_object* v___x_1262_; 
lean_inc(v_auxDeclToFullName_1258_);
lean_inc_ref(v_decls_1257_);
lean_inc_ref(v_fvarIdToDecl_1256_);
lean_dec_ref_known(v___x_1259_, 1);
lean_dec_ref(v_b_1228_);
v_index_1260_ = lean_ctor_get(v_localDecl_1255_, 0);
lean_inc(v_index_1260_);
v_fvarId_1261_ = lean_ctor_get(v_localDecl_1255_, 1);
lean_inc_ref(v_localDecl_1255_);
lean_inc(v_fvarId_1261_);
v___x_1262_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_fvarIdToDecl_1256_, v_fvarId_1261_, v_localDecl_1255_);
v___y_1242_ = v_decls_1257_;
v___y_1243_ = v_auxDeclToFullName_1258_;
v___y_1244_ = v___x_1262_;
v___y_1245_ = v_localDecl_1255_;
v___y_1246_ = v_index_1260_;
goto v___jp_1241_;
}
}
}
v___jp_1236_:
{
size_t v___x_1238_; size_t v___x_1239_; 
v___x_1238_ = ((size_t)1ULL);
v___x_1239_ = lean_usize_add(v_i_1227_, v___x_1238_);
v_i_1227_ = v___x_1239_;
v_b_1228_ = v_a_1237_;
goto _start;
}
v___jp_1241_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___y_1245_);
v___x_1248_ = l_Lean_PersistentArray_set___redArg(v___y_1242_, v___y_1246_, v___x_1247_);
lean_dec(v___y_1246_);
v___x_1249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1249_, 0, v___y_1244_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
lean_ctor_set(v___x_1249_, 2, v___y_1243_);
v_a_1237_ = v___x_1249_;
goto v___jp_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object* v_xs_1298_, lean_object* v_k_1299_, uint8_t v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_lctx_1307_; lean_object* v_localInstances_1308_; size_t v_sz_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v_lctx_1307_ = lean_ctor_get(v___y_1302_, 2);
v_localInstances_1308_ = lean_ctor_get(v___y_1302_, 3);
v_sz_1309_ = lean_array_size(v_xs_1298_);
v___x_1310_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1307_);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_xs_1298_, v_sz_1309_, v___x_1310_, v_lctx_1307_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
lean_inc_ref(v_localInstances_1308_);
v___x_1313_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_a_1312_, v_localInstances_1308_, v_k_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1313_;
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v_k_1299_);
v_a_1314_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1311_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1311_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object* v_xs_1322_, lean_object* v_k_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v___y_30430__boxed_1331_; lean_object* v_res_1332_; 
v___y_30430__boxed_1331_ = lean_unbox(v___y_1324_);
v_res_1332_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(v_xs_1322_, v_k_1323_, v___y_30430__boxed_1331_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v_xs_1322_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object* v___y_1333_, lean_object* v___f_1334_, lean_object* v_xs_1335_, lean_object* v_b_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
uint8_t v___y_30380__boxed_1344_; uint8_t v___y_30382__boxed_1345_; lean_object* v_res_1346_; 
v___y_30380__boxed_1344_ = lean_unbox(v___y_1333_);
v___y_30382__boxed_1345_ = lean_unbox(v___y_1337_);
v_res_1346_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(v___y_30380__boxed_1344_, v___f_1334_, v_xs_1335_, v_b_1336_, v___y_30382__boxed_1345_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object* v_b_1347_, lean_object* v_xs_1348_, uint8_t v___y_1349_, uint8_t v___x_1350_, uint8_t v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1347_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1358_, 1);
v___x_1360_ = 1;
v___x_1361_ = l_Lean_Meta_mkForallFVars(v_xs_1348_, v_a_1359_, v___y_1349_, v___x_1350_, v___x_1350_, v___x_1360_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
return v___x_1361_;
}
else
{
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object* v_b_1362_, lean_object* v_xs_1363_, lean_object* v___y_1364_, lean_object* v___x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
uint8_t v___y_30416__boxed_1373_; uint8_t v___x_30417__boxed_1374_; uint8_t v___y_30418__boxed_1375_; lean_object* v_res_1376_; 
v___y_30416__boxed_1373_ = lean_unbox(v___y_1364_);
v___x_30417__boxed_1374_ = lean_unbox(v___x_1365_);
v___y_30418__boxed_1375_ = lean_unbox(v___y_1366_);
v_res_1376_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(v_b_1362_, v_xs_1363_, v___y_30416__boxed_1373_, v___x_30417__boxed_1374_, v___y_30418__boxed_1375_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v_xs_1363_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t v___y_1377_, uint8_t v___x_1378_, lean_object* v___f_1379_, lean_object* v_xs_1380_, lean_object* v_b_1381_, uint8_t v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___f_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1389_ = lean_box(v___y_1377_);
v___x_1390_ = lean_box(v___x_1378_);
lean_inc_ref(v_xs_1380_);
v___f_1391_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1391_, 0, v_b_1381_);
lean_closure_set(v___f_1391_, 1, v_xs_1380_);
lean_closure_set(v___f_1391_, 2, v___x_1389_);
lean_closure_set(v___f_1391_, 3, v___x_1390_);
v___x_1392_ = lean_box(v___y_1382_);
lean_inc(v___y_1387_);
lean_inc_ref(v___y_1386_);
lean_inc(v___y_1385_);
lean_inc_ref(v___y_1384_);
lean_inc(v___y_1383_);
v___x_1393_ = lean_apply_9(v___f_1379_, v_xs_1380_, v___f_1391_, v___x_1392_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, lean_box(0));
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object* v___y_1394_, lean_object* v___x_1395_, lean_object* v___f_1396_, lean_object* v_xs_1397_, lean_object* v_b_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
uint8_t v___y_30391__boxed_1406_; uint8_t v___x_30392__boxed_1407_; uint8_t v___y_30394__boxed_1408_; lean_object* v_res_1409_; 
v___y_30391__boxed_1406_ = lean_unbox(v___y_1394_);
v___x_30392__boxed_1407_ = lean_unbox(v___x_1395_);
v___y_30394__boxed_1408_ = lean_unbox(v___y_1399_);
v_res_1409_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(v___y_30391__boxed_1406_, v___x_30392__boxed_1407_, v___f_1396_, v_xs_1397_, v_b_1398_, v___y_30394__boxed_1408_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t v_sz_1410_, size_t v_i_1411_, lean_object* v_bs_1412_, uint8_t v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_usize_dec_lt(v_i_1411_, v_sz_1410_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v_bs_1412_);
return v___x_1421_;
}
else
{
lean_object* v_v_1422_; lean_object* v___x_1423_; 
v_v_1422_ = lean_array_uget_borrowed(v_bs_1412_, v_i_1411_);
lean_inc(v_v_1422_);
v___x_1423_ = l_Lean_Meta_AbstractNestedProofs_visit(v_v_1422_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1425_; lean_object* v_bs_x27_1426_; size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = lean_unsigned_to_nat(0u);
v_bs_x27_1426_ = lean_array_uset(v_bs_1412_, v_i_1411_, v___x_1425_);
v___x_1427_ = ((size_t)1ULL);
v___x_1428_ = lean_usize_add(v_i_1411_, v___x_1427_);
v___x_1429_ = lean_array_uset(v_bs_x27_1426_, v_i_1411_, v_a_1424_);
v_i_1411_ = v___x_1428_;
v_bs_1412_ = v___x_1429_;
goto _start;
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref(v_bs_1412_);
v_a_1431_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1423_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1423_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, uint8_t v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
if (lean_obj_tag(v_x_1439_) == 5)
{
lean_object* v_fn_1449_; lean_object* v_arg_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v_fn_1449_ = lean_ctor_get(v_x_1439_, 0);
lean_inc_ref(v_fn_1449_);
v_arg_1450_ = lean_ctor_get(v_x_1439_, 1);
lean_inc_ref(v_arg_1450_);
lean_dec_ref_known(v_x_1439_, 2);
v___x_1451_ = lean_array_set(v_x_1440_, v_x_1441_, v_arg_1450_);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_sub(v_x_1441_, v___x_1452_);
lean_dec(v_x_1441_);
v_x_1439_ = v_fn_1449_;
v_x_1440_ = v___x_1451_;
v_x_1441_ = v___x_1453_;
goto _start;
}
else
{
lean_object* v___x_1455_; 
lean_dec(v_x_1441_);
v___x_1455_ = l_Lean_Meta_AbstractNestedProofs_visit(v_x_1439_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; size_t v_sz_1457_; size_t v___x_1458_; lean_object* v___x_1459_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v_sz_1457_ = lean_array_size(v_x_1440_);
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_1457_, v___x_1458_, v_x_1440_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1468_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1464_ = l_Lean_mkAppN(v_a_1456_, v_a_1460_);
lean_dec(v_a_1460_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1464_);
v___x_1466_ = v___x_1462_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_a_1456_);
v_a_1469_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1459_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1459_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_dec_ref(v_x_1440_);
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object* v_e_1477_, uint8_t v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v_a_1486_; lean_object* v___y_1492_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_visit___closed__0));
v___x_1495_ = l_Lean_Core_checkSystem(v___x_1494_, v_a_1482_, v_a_1483_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1562_; 
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v___x_1495_, 0);
lean_dec(v_unused_1563_);
v___x_1497_ = v___x_1495_;
v_isShared_1498_ = v_isSharedCheck_1562_;
goto v_resetjp_1496_;
}
else
{
lean_dec(v___x_1495_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1562_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
uint8_t v___x_1499_; 
v___x_1499_ = l_Lean_Expr_isAtomic(v_e_1477_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_st_ref_get(v_a_1479_);
v___x_1501_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v___x_1500_, v_e_1477_);
lean_dec(v___x_1500_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v___x_1502_; 
lean_del_object(v___x_1497_);
lean_inc_ref(v_e_1477_);
v___x_1502_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_1477_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___f_1507_; uint8_t v___x_1508_; uint8_t v___y_1510_; uint8_t v___x_1544_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1502_, 1);
v___f_1507_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed), 9, 0);
v___x_1508_ = 1;
v___x_1544_ = lean_unbox(v_a_1503_);
if (v___x_1544_ == 0)
{
uint8_t v___x_1545_; 
v___x_1545_ = lean_unbox(v_a_1503_);
lean_dec(v_a_1503_);
v___y_1510_ = v___x_1545_;
goto v___jp_1509_;
}
else
{
uint8_t v___x_1546_; 
lean_dec(v_a_1503_);
v___x_1546_ = l_Lean_Expr_hasSorry(v_e_1477_);
if (v___x_1546_ == 0)
{
lean_dec_ref(v___f_1507_);
goto v___jp_1504_;
}
else
{
if (v___x_1499_ == 0)
{
v___y_1510_ = v___x_1499_;
goto v___jp_1509_;
}
else
{
lean_dec_ref(v___f_1507_);
goto v___jp_1504_;
}
}
}
v___jp_1504_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___boxed), 8, 0);
lean_inc_ref(v_e_1477_);
v___x_1506_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_e_1477_, v_a_1478_, v___x_1505_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
v___y_1492_ = v___x_1506_;
goto v___jp_1491_;
}
v___jp_1509_:
{
switch(lean_obj_tag(v_e_1477_))
{
case 6:
{
lean_object* v___x_1511_; lean_object* v___f_1512_; lean_object* v___x_1513_; 
v___x_1511_ = lean_box(v___y_1510_);
v___f_1512_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1512_, 0, v___x_1511_);
lean_closure_set(v___f_1512_, 1, v___f_1507_);
lean_inc_ref(v_e_1477_);
v___x_1513_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1477_, v___f_1512_, v___y_1510_, v___x_1508_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
v___y_1492_ = v___x_1513_;
goto v___jp_1491_;
}
case 8:
{
lean_object* v___x_1514_; lean_object* v___f_1515_; lean_object* v___x_1516_; 
v___x_1514_ = lean_box(v___y_1510_);
v___f_1515_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1515_, 0, v___x_1514_);
lean_closure_set(v___f_1515_, 1, v___f_1507_);
lean_inc_ref(v_e_1477_);
v___x_1516_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1477_, v___f_1515_, v___y_1510_, v___x_1508_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
v___y_1492_ = v___x_1516_;
goto v___jp_1491_;
}
case 7:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___f_1519_; lean_object* v___x_1520_; 
v___x_1517_ = lean_box(v___y_1510_);
v___x_1518_ = lean_box(v___x_1508_);
v___f_1519_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed), 12, 3);
lean_closure_set(v___f_1519_, 0, v___x_1517_);
lean_closure_set(v___f_1519_, 1, v___x_1518_);
lean_closure_set(v___f_1519_, 2, v___f_1507_);
lean_inc_ref(v_e_1477_);
v___x_1520_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_e_1477_, v___f_1519_, v___y_1510_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
v___y_1492_ = v___x_1520_;
goto v___jp_1491_;
}
case 10:
{
lean_object* v_data_1521_; lean_object* v_expr_1522_; lean_object* v___x_1523_; 
lean_dec_ref(v___f_1507_);
v_data_1521_ = lean_ctor_get(v_e_1477_, 0);
v_expr_1522_ = lean_ctor_get(v_e_1477_, 1);
lean_inc_ref(v_expr_1522_);
v___x_1523_ = l_Lean_Meta_AbstractNestedProofs_visit(v_expr_1522_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; size_t v___x_1525_; size_t v___x_1526_; uint8_t v___x_1527_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v___x_1525_ = lean_ptr_addr(v_expr_1522_);
v___x_1526_ = lean_ptr_addr(v_a_1524_);
v___x_1527_ = lean_usize_dec_eq(v___x_1525_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; 
lean_inc(v_data_1521_);
v___x_1528_ = l_Lean_Expr_mdata___override(v_data_1521_, v_a_1524_);
v_a_1486_ = v___x_1528_;
goto v___jp_1485_;
}
else
{
lean_dec(v_a_1524_);
lean_inc_ref(v_e_1477_);
v_a_1486_ = v_e_1477_;
goto v___jp_1485_;
}
}
else
{
v___y_1492_ = v___x_1523_;
goto v___jp_1491_;
}
}
case 11:
{
lean_object* v_typeName_1529_; lean_object* v_idx_1530_; lean_object* v_struct_1531_; lean_object* v___x_1532_; 
lean_dec_ref(v___f_1507_);
v_typeName_1529_ = lean_ctor_get(v_e_1477_, 0);
v_idx_1530_ = lean_ctor_get(v_e_1477_, 1);
v_struct_1531_ = lean_ctor_get(v_e_1477_, 2);
lean_inc_ref(v_struct_1531_);
v___x_1532_ = l_Lean_Meta_AbstractNestedProofs_visit(v_struct_1531_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; size_t v___x_1534_; size_t v___x_1535_; uint8_t v___x_1536_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = lean_ptr_addr(v_struct_1531_);
v___x_1535_ = lean_ptr_addr(v_a_1533_);
v___x_1536_ = lean_usize_dec_eq(v___x_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
lean_inc(v_idx_1530_);
lean_inc(v_typeName_1529_);
v___x_1537_ = l_Lean_Expr_proj___override(v_typeName_1529_, v_idx_1530_, v_a_1533_);
v_a_1486_ = v___x_1537_;
goto v___jp_1485_;
}
else
{
lean_dec(v_a_1533_);
lean_inc_ref(v_e_1477_);
v_a_1486_ = v_e_1477_;
goto v___jp_1485_;
}
}
else
{
v___y_1492_ = v___x_1532_;
goto v___jp_1491_;
}
}
case 5:
{
lean_object* v_dummy_1538_; lean_object* v_nargs_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec_ref(v___f_1507_);
v_dummy_1538_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_1539_ = l_Lean_Expr_getAppNumArgs(v_e_1477_);
lean_inc(v_nargs_1539_);
v___x_1540_ = lean_mk_array(v_nargs_1539_, v_dummy_1538_);
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = lean_nat_sub(v_nargs_1539_, v___x_1541_);
lean_dec(v_nargs_1539_);
lean_inc_ref(v_e_1477_);
v___x_1543_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_e_1477_, v___x_1540_, v___x_1542_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
v___y_1492_ = v___x_1543_;
goto v___jp_1491_;
}
default: 
{
lean_dec_ref(v___f_1507_);
lean_inc_ref(v_e_1477_);
v_a_1486_ = v_e_1477_;
goto v___jp_1485_;
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref(v_e_1477_);
v_a_1547_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1502_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1502_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_val_1555_; lean_object* v___x_1557_; 
lean_dec_ref(v_e_1477_);
v_val_1555_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v___x_1501_, 1);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v_val_1555_);
v___x_1557_ = v___x_1497_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_val_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
else
{
lean_object* v___x_1560_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v_e_1477_);
v___x_1560_ = v___x_1497_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_e_1477_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v_e_1477_);
v_a_1564_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1495_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1495_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
v___jp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1487_ = lean_st_ref_take(v_a_1479_);
lean_inc_ref(v_a_1486_);
v___x_1488_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v___x_1487_, v_e_1477_, v_a_1486_);
v___x_1489_ = lean_st_ref_set(v_a_1479_, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_a_1486_);
return v___x_1490_;
}
v___jp_1491_:
{
if (lean_obj_tag(v___y_1492_) == 0)
{
lean_object* v_a_1493_; 
v_a_1493_ = lean_ctor_get(v___y_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___y_1492_, 1);
v_a_1486_ = v_a_1493_;
goto v___jp_1485_;
}
else
{
lean_dec_ref(v_e_1477_);
return v___y_1492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object* v_b_1572_, lean_object* v_xs_1573_, uint8_t v___y_1574_, uint8_t v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1572_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; uint8_t v___x_1584_; lean_object* v___x_1585_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = 1;
v___x_1585_ = l_Lean_Meta_mkLambdaFVars(v_xs_1573_, v_a_1583_, v___y_1574_, v___y_1574_, v___y_1574_, v___y_1574_, v___x_1584_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
return v___x_1585_;
}
else
{
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object* v_b_1586_, lean_object* v_xs_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
uint8_t v___y_30403__boxed_1596_; uint8_t v___y_30404__boxed_1597_; lean_object* v_res_1598_; 
v___y_30403__boxed_1596_ = lean_unbox(v___y_1588_);
v___y_30404__boxed_1597_ = lean_unbox(v___y_1589_);
v_res_1598_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(v_b_1586_, v_xs_1587_, v___y_30403__boxed_1596_, v___y_30404__boxed_1597_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v_xs_1587_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t v___y_1599_, lean_object* v___f_1600_, lean_object* v_xs_1601_, lean_object* v_b_1602_, uint8_t v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; lean_object* v___f_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1610_ = lean_box(v___y_1599_);
lean_inc_ref(v_xs_1601_);
v___f_1611_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1611_, 0, v_b_1602_);
lean_closure_set(v___f_1611_, 1, v_xs_1601_);
lean_closure_set(v___f_1611_, 2, v___x_1610_);
v___x_1612_ = lean_box(v___y_1603_);
lean_inc(v___y_1608_);
lean_inc_ref(v___y_1607_);
lean_inc(v___y_1606_);
lean_inc_ref(v___y_1605_);
lean_inc(v___y_1604_);
v___x_1613_ = lean_apply_9(v___f_1600_, v_xs_1601_, v___f_1611_, v___x_1612_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, lean_box(0));
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object* v_sz_1614_, lean_object* v_i_1615_, lean_object* v_bs_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
size_t v_sz_boxed_1624_; size_t v_i_boxed_1625_; uint8_t v___y_30443__boxed_1626_; lean_object* v_res_1627_; 
v_sz_boxed_1624_ = lean_unbox_usize(v_sz_1614_);
lean_dec(v_sz_1614_);
v_i_boxed_1625_ = lean_unbox_usize(v_i_1615_);
lean_dec(v_i_1615_);
v___y_30443__boxed_1626_ = lean_unbox(v___y_1617_);
v_res_1627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_boxed_1624_, v_i_boxed_1625_, v_bs_1616_, v___y_30443__boxed_1626_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object* v_x_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
uint8_t v___y_30464__boxed_1638_; lean_object* v_res_1639_; 
v___y_30464__boxed_1638_ = lean_unbox(v___y_1631_);
v_res_1639_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_x_1628_, v_x_1629_, v_x_1630_, v___y_30464__boxed_1638_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object* v_as_1640_, lean_object* v_sz_1641_, lean_object* v_i_1642_, lean_object* v_b_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
size_t v_sz_boxed_1651_; size_t v_i_boxed_1652_; uint8_t v___y_30487__boxed_1653_; lean_object* v_res_1654_; 
v_sz_boxed_1651_ = lean_unbox_usize(v_sz_1641_);
lean_dec(v_sz_1641_);
v_i_boxed_1652_ = lean_unbox_usize(v_i_1642_);
lean_dec(v_i_1642_);
v___y_30487__boxed_1653_ = lean_unbox(v___y_1644_);
v_res_1654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_as_1640_, v_sz_boxed_1651_, v_i_boxed_1652_, v_b_1643_, v___y_30487__boxed_1653_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v_as_1640_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object* v_00_u03b2_1655_, lean_object* v_m_1656_, lean_object* v_a_1657_, lean_object* v_b_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_m_1656_, v_a_1657_, v_b_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object* v_00_u03b2_1660_, lean_object* v_m_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_1661_, v_a_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object* v_00_u03b2_1664_, lean_object* v_m_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_00_u03b2_1664_, v_m_1665_, v_a_1666_);
lean_dec_ref(v_a_1666_);
lean_dec_ref(v_m_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object* v_00_u03b2_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_x_1669_, v_x_1670_, v_x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object* v_00_u03b2_1673_, lean_object* v_a_1674_, lean_object* v_x_1675_){
_start:
{
uint8_t v___x_1676_; 
v___x_1676_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1674_, v_x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1677_, lean_object* v_a_1678_, lean_object* v_x_1679_){
_start:
{
uint8_t v_res_1680_; lean_object* v_r_1681_; 
v_res_1680_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(v_00_u03b2_1677_, v_a_1678_, v_x_1679_);
lean_dec(v_x_1679_);
lean_dec_ref(v_a_1678_);
v_r_1681_ = lean_box(v_res_1680_);
return v_r_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2(lean_object* v_00_u03b2_1682_, lean_object* v_data_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(v_data_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3(lean_object* v_00_u03b2_1685_, lean_object* v_a_1686_, lean_object* v_b_1687_, lean_object* v_x_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1686_, v_b_1687_, v_x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(lean_object* v_00_u03b2_1690_, lean_object* v_a_1691_, lean_object* v_x_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_1691_, v_x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1694_, lean_object* v_a_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(v_00_u03b2_1694_, v_a_1695_, v_x_1696_);
lean_dec(v_x_1696_);
lean_dec_ref(v_a_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b1_1698_, lean_object* v_x_1699_, uint8_t v_isExporting_1700_, uint8_t v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_x_1699_, v_isExporting_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___boxed(lean_object* v_00_u03b1_1709_, lean_object* v_x_1710_, lean_object* v_isExporting_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
uint8_t v_isExporting_boxed_1719_; uint8_t v___y_31084__boxed_1720_; lean_object* v_res_1721_; 
v_isExporting_boxed_1719_ = lean_unbox(v_isExporting_1711_);
v___y_31084__boxed_1720_ = lean_unbox(v___y_1712_);
v_res_1721_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(v_00_u03b1_1709_, v_x_1710_, v_isExporting_boxed_1719_, v___y_31084__boxed_1720_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(lean_object* v_00_u03b1_1722_, lean_object* v_x_1723_, uint8_t v_when_1724_, uint8_t v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_1723_, v_when_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1733_, lean_object* v_x_1734_, lean_object* v_when_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
uint8_t v_when_boxed_1743_; uint8_t v___y_31107__boxed_1744_; lean_object* v_res_1745_; 
v_when_boxed_1743_ = lean_unbox(v_when_1735_);
v___y_31107__boxed_1744_ = lean_unbox(v___y_1736_);
v_res_1745_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(v_00_u03b1_1733_, v_x_1734_, v_when_boxed_1743_, v___y_31107__boxed_1744_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9(lean_object* v_00_u03b2_1746_, lean_object* v_x_1747_, size_t v_x_1748_, size_t v_x_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___redArg(v_x_1747_, v_x_1748_, v_x_1749_, v_x_1750_, v_x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1753_, lean_object* v_x_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
size_t v_x_31131__boxed_1759_; size_t v_x_31132__boxed_1760_; lean_object* v_res_1761_; 
v_x_31131__boxed_1759_ = lean_unbox_usize(v_x_1755_);
lean_dec(v_x_1755_);
v_x_31132__boxed_1760_ = lean_unbox_usize(v_x_1756_);
lean_dec(v_x_1756_);
v_res_1761_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9(v_00_u03b2_1753_, v_x_1754_, v_x_31131__boxed_1759_, v_x_31132__boxed_1760_, v_x_1757_, v_x_1758_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1762_, lean_object* v_i_1763_, lean_object* v_source_1764_, lean_object* v_target_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(v_i_1763_, v_source_1764_, v_target_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15(lean_object* v_00_u03b2_1767_, lean_object* v_n_1768_, lean_object* v_k_1769_, lean_object* v_v_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15___redArg(v_n_1768_, v_k_1769_, v_v_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16(lean_object* v_00_u03b2_1772_, size_t v_depth_1773_, lean_object* v_keys_1774_, lean_object* v_vals_1775_, lean_object* v_heq_1776_, lean_object* v_i_1777_, lean_object* v_entries_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___redArg(v_depth_1773_, v_keys_1774_, v_vals_1775_, v_i_1777_, v_entries_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1780_, lean_object* v_depth_1781_, lean_object* v_keys_1782_, lean_object* v_vals_1783_, lean_object* v_heq_1784_, lean_object* v_i_1785_, lean_object* v_entries_1786_){
_start:
{
size_t v_depth_boxed_1787_; lean_object* v_res_1788_; 
v_depth_boxed_1787_ = lean_unbox_usize(v_depth_1781_);
lean_dec(v_depth_1781_);
v_res_1788_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__16(v_00_u03b2_1780_, v_depth_boxed_1787_, v_keys_1782_, v_vals_1783_, v_heq_1784_, v_i_1785_, v_entries_1786_);
lean_dec_ref(v_vals_1783_);
lean_dec_ref(v_keys_1782_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(v_x_1790_, v_x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19(lean_object* v_00_u03b2_1793_, lean_object* v_x_1794_, lean_object* v_x_1795_, lean_object* v_x_1796_, lean_object* v_x_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__9_spec__15_spec__19___redArg(v_x_1794_, v_x_1795_, v_x_1796_, v_x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__0(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = lean_unsigned_to_nat(16u);
v___x_1801_ = lean_mk_array(v___x_1800_, v___x_1799_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__1(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__0, &l_Lean_Meta_abstractNestedProofs___closed__0_once, _init_l_Lean_Meta_abstractNestedProofs___closed__0);
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
lean_ctor_set(v___x_1804_, 1, v___x_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs(lean_object* v_e_1805_, uint8_t v_cache_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v___x_1812_; 
lean_inc_ref(v_e_1805_);
v___x_1812_ = l_Lean_Meta_isProof(v_e_1805_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1833_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1833_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1833_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_unbox(v_a_1813_);
lean_dec(v_a_1813_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_del_object(v___x_1815_);
v___x_1818_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__1, &l_Lean_Meta_abstractNestedProofs___closed__1_once, _init_l_Lean_Meta_abstractNestedProofs___closed__1);
v___x_1819_ = lean_st_mk_ref(v___x_1818_);
v___x_1820_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1805_, v_cache_1806_, v___x_1819_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1829_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1829_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1829_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1825_ = lean_st_ref_get(v___x_1819_);
lean_dec(v___x_1819_);
lean_dec(v___x_1825_);
if (v_isShared_1824_ == 0)
{
v___x_1827_ = v___x_1823_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1821_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
else
{
lean_dec(v___x_1819_);
return v___x_1820_;
}
}
else
{
lean_object* v___x_1831_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v_e_1805_);
v___x_1831_ = v___x_1815_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_e_1805_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v_e_1805_);
v_a_1834_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1812_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1812_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object* v_e_1842_, lean_object* v_cache_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
uint8_t v_cache_boxed_1849_; lean_object* v_res_1850_; 
v_cache_boxed_1849_ = lean_unbox(v_cache_1843_);
v_res_1850_ = l_Lean_Meta_abstractNestedProofs(v_e_1842_, v_cache_boxed_1849_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
return v_res_1850_;
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
