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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
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
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "abstract nested proofs"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_visit___closed__0 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_a_4103__boxed_143_; uint8_t v___x_4104__boxed_144_; size_t v_i_boxed_145_; size_t v_stop_boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v_a_4103__boxed_143_ = lean_unbox(v_a_138_);
v___x_4104__boxed_144_ = lean_unbox(v___x_139_);
v_i_boxed_145_ = lean_unbox_usize(v_i_141_);
lean_dec(v_i_141_);
v_stop_boxed_146_ = lean_unbox_usize(v_stop_142_);
lean_dec(v_stop_142_);
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_4103__boxed_143_, v___x_4104__boxed_144_, v_as_140_, v_i_boxed_145_, v_stop_boxed_146_);
lean_dec_ref(v_as_140_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(uint8_t v_a_149_, uint8_t v___x_150_, lean_object* v___x_151_, lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg___boxed(lean_object* v_a_184_, lean_object* v___x_185_, lean_object* v___x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v___y_190_){
_start:
{
uint8_t v_a_4129__boxed_191_; uint8_t v___x_4130__boxed_192_; lean_object* v_res_193_; 
v_a_4129__boxed_191_ = lean_unbox(v_a_184_);
v___x_4130__boxed_192_ = lean_unbox(v___x_185_);
v_res_193_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(v_a_4129__boxed_191_, v___x_4130__boxed_192_, v___x_186_, v_x_187_, v_x_188_, v_x_189_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(uint8_t v_a_194_, uint8_t v___x_195_, lean_object* v___x_196_, lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
if (lean_obj_tag(v_x_197_) == 5)
{
lean_object* v_fn_218_; lean_object* v_arg_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_fn_218_ = lean_ctor_get(v_x_197_, 0);
lean_inc_ref(v_fn_218_);
v_arg_219_ = lean_ctor_get(v_x_197_, 1);
lean_inc_ref(v_arg_219_);
lean_dec_ref_known(v_x_197_, 2);
v___x_220_ = lean_array_set(v_x_198_, v_x_199_, v_arg_219_);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_sub(v_x_199_, v___x_221_);
v___x_223_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(v_a_194_, v___x_195_, v___x_196_, v_fn_218_, v___x_220_, v___x_222_);
return v___x_223_;
}
else
{
uint8_t v___x_224_; 
v___x_224_ = l_Lean_Expr_isAtomic(v_x_197_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v_x_198_);
lean_dec_ref(v_x_197_);
lean_dec_ref(v___x_196_);
v___x_225_ = lean_box(v_a_194_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
else
{
if (v___x_195_ == 0)
{
if (lean_obj_tag(v_x_197_) == 4)
{
lean_object* v_declName_227_; uint8_t v___x_228_; 
v_declName_227_ = lean_ctor_get(v_x_197_, 0);
lean_inc(v_declName_227_);
lean_dec_ref_known(v_x_197_, 2);
v___x_228_ = l_Lean_Environment_contains(v___x_196_, v_declName_227_, v_a_194_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec_ref(v_x_198_);
v___x_229_ = lean_box(v_a_194_);
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
else
{
goto v___jp_205_;
}
}
else
{
lean_dec_ref(v_x_197_);
lean_dec_ref(v___x_196_);
goto v___jp_205_;
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec_ref(v_x_198_);
lean_dec_ref(v_x_197_);
lean_dec_ref(v___x_196_);
v___x_231_ = lean_box(v_a_194_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
}
v___jp_205_:
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_array_get_size(v_x_198_);
v___x_208_ = lean_nat_dec_lt(v___x_206_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec_ref(v_x_198_);
v___x_209_ = lean_box(v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
else
{
if (v___x_208_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec_ref(v_x_198_);
v___x_211_ = lean_box(v___x_208_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
else
{
size_t v___x_213_; size_t v___x_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_213_ = ((size_t)0ULL);
v___x_214_ = lean_usize_of_nat(v___x_207_);
v___x_215_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_194_, v___x_195_, v_x_198_, v___x_213_, v___x_214_);
lean_dec_ref(v_x_198_);
v___x_216_ = lean_box(v___x_215_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object* v_a_233_, lean_object* v___x_234_, lean_object* v___x_235_, lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
uint8_t v_a_4207__boxed_244_; uint8_t v___x_4208__boxed_245_; lean_object* v_res_246_; 
v_a_4207__boxed_244_ = lean_unbox(v_a_233_);
v___x_4208__boxed_245_ = lean_unbox(v___x_234_);
v_res_246_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(v_a_4207__boxed_244_, v___x_4208__boxed_245_, v___x_235_, v_x_236_, v_x_237_, v_x_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v_x_238_);
return v_res_246_;
}
}
static lean_object* _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4(void){
_start:
{
lean_object* v___x_254_; lean_object* v_dummy_255_; 
v___x_254_ = lean_box(0);
v_dummy_255_ = l_Lean_Expr_sort___override(v___x_254_);
return v_dummy_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(lean_object* v_e_256_, lean_object* v_env_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_263_; 
lean_inc_ref(v_e_256_);
v___x_263_ = l_Lean_Meta_isProof(v_e_256_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; uint8_t v___x_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
v___x_265_ = lean_unbox(v_a_264_);
if (v___x_265_ == 0)
{
lean_dec(v_a_264_);
lean_dec_ref(v_env_257_);
lean_dec_ref(v_e_256_);
return v___x_263_;
}
else
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_284_; 
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; 
v_unused_285_ = lean_ctor_get(v___x_263_, 0);
lean_dec(v_unused_285_);
v___x_267_ = v___x_263_;
v_isShared_268_ = v_isSharedCheck_284_;
goto v_resetjp_266_;
}
else
{
lean_dec(v___x_263_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_284_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3));
v___x_270_ = l_Lean_Expr_isAppOf(v_e_256_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v_dummy_272_; lean_object* v_nargs_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; lean_object* v___x_278_; 
lean_del_object(v___x_267_);
v___x_271_ = l_Lean_Meta_AbstractNestedProofs_getLambdaBody(v_e_256_);
lean_dec_ref(v_e_256_);
v_dummy_272_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_273_ = l_Lean_Expr_getAppNumArgs(v___x_271_);
lean_inc(v_nargs_273_);
v___x_274_ = lean_mk_array(v_nargs_273_, v_dummy_272_);
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_sub(v_nargs_273_, v___x_275_);
lean_dec(v_nargs_273_);
v___x_277_ = lean_unbox(v_a_264_);
lean_dec(v_a_264_);
v___x_278_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(v___x_277_, v___x_270_, v_env_257_, v___x_271_, v___x_274_, v___x_276_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___x_276_);
return v___x_278_;
}
else
{
uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
lean_dec(v_a_264_);
lean_dec_ref(v_env_257_);
lean_dec_ref(v_e_256_);
v___x_279_ = 0;
v___x_280_ = lean_box(v___x_279_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_280_);
v___x_282_ = v___x_267_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_257_);
lean_dec_ref(v_e_256_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed(lean_object* v_e_286_, lean_object* v_env_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(v_e_286_, v_env_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(lean_object* v___y_294_, uint8_t v_isExporting_295_, lean_object* v___x_296_, lean_object* v___y_297_, lean_object* v___x_298_, lean_object* v_a_x3f_299_){
_start:
{
lean_object* v___x_301_; lean_object* v_env_302_; lean_object* v_nextMacroScope_303_; lean_object* v_ngen_304_; lean_object* v_auxDeclNGen_305_; lean_object* v_traceState_306_; lean_object* v_recordedDeps_307_; lean_object* v_messages_308_; lean_object* v_infoState_309_; lean_object* v_snapshotTasks_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_335_; 
v___x_301_ = lean_st_ref_take(v___y_294_);
v_env_302_ = lean_ctor_get(v___x_301_, 0);
v_nextMacroScope_303_ = lean_ctor_get(v___x_301_, 1);
v_ngen_304_ = lean_ctor_get(v___x_301_, 2);
v_auxDeclNGen_305_ = lean_ctor_get(v___x_301_, 3);
v_traceState_306_ = lean_ctor_get(v___x_301_, 4);
v_recordedDeps_307_ = lean_ctor_get(v___x_301_, 6);
v_messages_308_ = lean_ctor_get(v___x_301_, 7);
v_infoState_309_ = lean_ctor_get(v___x_301_, 8);
v_snapshotTasks_310_ = lean_ctor_get(v___x_301_, 9);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v___x_301_, 5);
lean_dec(v_unused_336_);
v___x_312_ = v___x_301_;
v_isShared_313_ = v_isSharedCheck_335_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_snapshotTasks_310_);
lean_inc(v_infoState_309_);
lean_inc(v_messages_308_);
lean_inc(v_recordedDeps_307_);
lean_inc(v_traceState_306_);
lean_inc(v_auxDeclNGen_305_);
lean_inc(v_ngen_304_);
lean_inc(v_nextMacroScope_303_);
lean_inc(v_env_302_);
lean_dec(v___x_301_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_335_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_314_ = l_Lean_Environment_setExporting(v_env_302_, v_isExporting_295_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 5, v___x_296_);
lean_ctor_set(v___x_312_, 0, v___x_314_);
v___x_316_ = v___x_312_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_nextMacroScope_303_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_ngen_304_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_auxDeclNGen_305_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v_traceState_306_);
lean_ctor_set(v_reuseFailAlloc_334_, 5, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_334_, 6, v_recordedDeps_307_);
lean_ctor_set(v_reuseFailAlloc_334_, 7, v_messages_308_);
lean_ctor_set(v_reuseFailAlloc_334_, 8, v_infoState_309_);
lean_ctor_set(v_reuseFailAlloc_334_, 9, v_snapshotTasks_310_);
v___x_316_ = v_reuseFailAlloc_334_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_mctx_319_; lean_object* v_zetaDeltaFVarIds_320_; lean_object* v_postponed_321_; lean_object* v_diag_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_332_; 
v___x_317_ = lean_st_ref_put(v___y_294_, v___x_316_);
v___x_318_ = lean_st_ref_take(v___y_297_);
v_mctx_319_ = lean_ctor_get(v___x_318_, 0);
v_zetaDeltaFVarIds_320_ = lean_ctor_get(v___x_318_, 2);
v_postponed_321_ = lean_ctor_get(v___x_318_, 3);
v_diag_322_ = lean_ctor_get(v___x_318_, 4);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v___x_318_, 1);
lean_dec(v_unused_333_);
v___x_324_ = v___x_318_;
v_isShared_325_ = v_isSharedCheck_332_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_diag_322_);
lean_inc(v_postponed_321_);
lean_inc(v_zetaDeltaFVarIds_320_);
lean_inc(v_mctx_319_);
lean_dec(v___x_318_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_332_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = lean_box(0);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v___x_298_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_mctx_319_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_zetaDeltaFVarIds_320_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v_postponed_321_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v_diag_322_);
v___x_328_ = v_reuseFailAlloc_331_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_st_ref_put(v___y_297_, v___x_328_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_326_);
return v___x_330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v___y_337_, lean_object* v_isExporting_338_, lean_object* v___x_339_, lean_object* v___y_340_, lean_object* v___x_341_, lean_object* v_a_x3f_342_, lean_object* v___y_343_){
_start:
{
uint8_t v_isExporting_boxed_344_; lean_object* v_res_345_; 
v_isExporting_boxed_344_ = lean_unbox(v_isExporting_338_);
v_res_345_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_337_, v_isExporting_boxed_344_, v___x_339_, v___y_340_, v___x_341_, v_a_x3f_342_);
lean_dec(v_a_x3f_342_);
lean_dec(v___y_340_);
lean_dec(v___y_337_);
return v_res_345_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_346_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1);
v___x_352_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
lean_ctor_set(v___x_352_, 2, v___x_351_);
lean_ctor_set(v___x_352_, 3, v___x_351_);
lean_ctor_set(v___x_352_, 4, v___x_351_);
lean_ctor_set(v___x_352_, 5, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(lean_object* v_x_353_, uint8_t v_isExporting_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; lean_object* v_env_361_; lean_object* v___x_362_; uint8_t v_isModule_363_; 
v___x_360_ = lean_st_ref_get(v___y_358_);
v_env_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc_ref(v_env_361_);
lean_dec(v___x_360_);
v___x_362_ = l_Lean_Environment_header(v_env_361_);
v_isModule_363_ = lean_ctor_get_uint8(v___x_362_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_362_);
if (v_isModule_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec_ref(v_env_361_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_356_);
lean_inc_ref(v___y_355_);
v___x_364_ = lean_apply_5(v_x_353_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, lean_box(0));
return v___x_364_;
}
else
{
uint8_t v_isExporting_365_; 
v_isExporting_365_ = lean_ctor_get_uint8(v_env_361_, sizeof(void*)*8);
lean_dec_ref(v_env_361_);
if (v_isExporting_354_ == 0)
{
if (v_isExporting_365_ == 0)
{
lean_object* v___x_432_; 
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_356_);
lean_inc_ref(v___y_355_);
v___x_432_ = lean_apply_5(v_x_353_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, lean_box(0));
return v___x_432_;
}
else
{
goto v___jp_366_;
}
}
else
{
if (v_isExporting_365_ == 0)
{
goto v___jp_366_;
}
else
{
lean_object* v___x_433_; 
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_356_);
lean_inc_ref(v___y_355_);
v___x_433_ = lean_apply_5(v_x_353_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, lean_box(0));
return v___x_433_;
}
}
v___jp_366_:
{
lean_object* v___x_367_; lean_object* v_env_368_; lean_object* v_nextMacroScope_369_; lean_object* v_ngen_370_; lean_object* v_auxDeclNGen_371_; lean_object* v_traceState_372_; lean_object* v_recordedDeps_373_; lean_object* v_messages_374_; lean_object* v_infoState_375_; lean_object* v_snapshotTasks_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_430_; 
v___x_367_ = lean_st_ref_take(v___y_358_);
v_env_368_ = lean_ctor_get(v___x_367_, 0);
v_nextMacroScope_369_ = lean_ctor_get(v___x_367_, 1);
v_ngen_370_ = lean_ctor_get(v___x_367_, 2);
v_auxDeclNGen_371_ = lean_ctor_get(v___x_367_, 3);
v_traceState_372_ = lean_ctor_get(v___x_367_, 4);
v_recordedDeps_373_ = lean_ctor_get(v___x_367_, 6);
v_messages_374_ = lean_ctor_get(v___x_367_, 7);
v_infoState_375_ = lean_ctor_get(v___x_367_, 8);
v_snapshotTasks_376_ = lean_ctor_get(v___x_367_, 9);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v___x_367_, 5);
lean_dec(v_unused_431_);
v___x_378_ = v___x_367_;
v_isShared_379_ = v_isSharedCheck_430_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_snapshotTasks_376_);
lean_inc(v_infoState_375_);
lean_inc(v_messages_374_);
lean_inc(v_recordedDeps_373_);
lean_inc(v_traceState_372_);
lean_inc(v_auxDeclNGen_371_);
lean_inc(v_ngen_370_);
lean_inc(v_nextMacroScope_369_);
lean_inc(v_env_368_);
lean_dec(v___x_367_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_430_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_380_ = l_Lean_Environment_setExporting(v_env_368_, v_isExporting_354_);
v___x_381_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 5, v___x_381_);
lean_ctor_set(v___x_378_, 0, v___x_380_);
v___x_383_ = v___x_378_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_nextMacroScope_369_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_ngen_370_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v_auxDeclNGen_371_);
lean_ctor_set(v_reuseFailAlloc_429_, 4, v_traceState_372_);
lean_ctor_set(v_reuseFailAlloc_429_, 5, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_429_, 6, v_recordedDeps_373_);
lean_ctor_set(v_reuseFailAlloc_429_, 7, v_messages_374_);
lean_ctor_set(v_reuseFailAlloc_429_, 8, v_infoState_375_);
lean_ctor_set(v_reuseFailAlloc_429_, 9, v_snapshotTasks_376_);
v___x_383_ = v_reuseFailAlloc_429_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_mctx_386_; lean_object* v_zetaDeltaFVarIds_387_; lean_object* v_postponed_388_; lean_object* v_diag_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_427_; 
v___x_384_ = lean_st_ref_put(v___y_358_, v___x_383_);
v___x_385_ = lean_st_ref_take(v___y_356_);
v_mctx_386_ = lean_ctor_get(v___x_385_, 0);
v_zetaDeltaFVarIds_387_ = lean_ctor_get(v___x_385_, 2);
v_postponed_388_ = lean_ctor_get(v___x_385_, 3);
v_diag_389_ = lean_ctor_get(v___x_385_, 4);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; 
v_unused_428_ = lean_ctor_get(v___x_385_, 1);
lean_dec(v_unused_428_);
v___x_391_ = v___x_385_;
v_isShared_392_ = v_isSharedCheck_427_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_diag_389_);
lean_inc(v_postponed_388_);
lean_inc(v_zetaDeltaFVarIds_387_);
lean_inc(v_mctx_386_);
lean_dec(v___x_385_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_427_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_393_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v___x_393_);
v___x_395_ = v___x_391_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_mctx_386_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_zetaDeltaFVarIds_387_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_postponed_388_);
lean_ctor_set(v_reuseFailAlloc_426_, 4, v_diag_389_);
v___x_395_ = v_reuseFailAlloc_426_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; lean_object* v_r_397_; 
v___x_396_ = lean_st_ref_put(v___y_356_, v___x_395_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_356_);
lean_inc_ref(v___y_355_);
v_r_397_ = lean_apply_5(v_x_353_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, lean_box(0));
if (lean_obj_tag(v_r_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_414_; 
v_a_398_ = lean_ctor_get(v_r_397_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_r_397_);
if (v_isSharedCheck_414_ == 0)
{
v___x_400_ = v_r_397_;
v_isShared_401_ = v_isSharedCheck_414_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v_r_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_414_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
lean_inc(v_a_398_);
if (v_isShared_401_ == 0)
{
lean_ctor_set_tag(v___x_400_, 1);
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_413_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
v___x_404_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_358_, v_isExporting_365_, v___x_381_, v___y_356_, v___x_393_, v___x_403_);
lean_dec_ref(v___x_403_);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_404_, 0);
lean_dec(v_unused_412_);
v___x_406_ = v___x_404_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_dec(v___x_404_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v_a_398_);
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_398_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
v_a_415_ = lean_ctor_get(v_r_397_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v_r_397_, 1);
v___x_416_ = lean_box(0);
v___x_417_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_358_, v_isExporting_365_, v___x_381_, v___y_356_, v___x_393_, v___x_416_);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v___x_417_, 0);
lean_dec(v_unused_425_);
v___x_419_ = v___x_417_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_dec(v___x_417_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 1);
lean_ctor_set(v___x_419_, 0, v_a_415_);
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_415_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___boxed(lean_object* v_x_434_, lean_object* v_isExporting_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
uint8_t v_isExporting_boxed_441_; lean_object* v_res_442_; 
v_isExporting_boxed_441_ = lean_unbox(v_isExporting_435_);
v_res_442_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(v_x_434_, v_isExporting_boxed_441_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object* v_x_443_, uint8_t v_when_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
if (v_when_444_ == 0)
{
lean_object* v___x_450_; 
lean_inc(v___y_448_);
lean_inc_ref(v___y_447_);
lean_inc(v___y_446_);
lean_inc_ref(v___y_445_);
v___x_450_ = lean_apply_5(v_x_443_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, lean_box(0));
return v___x_450_;
}
else
{
uint8_t v___x_451_; lean_object* v___x_452_; 
v___x_451_ = 0;
v___x_452_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(v_x_443_, v___x_451_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object* v_x_453_, lean_object* v_when_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
uint8_t v_when_boxed_460_; lean_object* v_res_461_; 
v_when_boxed_460_ = lean_unbox(v_when_454_);
v_res_461_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_453_, v_when_boxed_460_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object* v_e_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_468_; lean_object* v_env_469_; lean_object* v___f_470_; uint8_t v___x_471_; lean_object* v___x_472_; 
v___x_468_ = lean_st_ref_get(v_a_466_);
v_env_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc_ref(v_env_469_);
lean_dec(v___x_468_);
v___f_470_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed), 7, 2);
lean_closure_set(v___f_470_, 0, v_e_462_);
lean_closure_set(v___f_470_, 1, v_env_469_);
v___x_471_ = 1;
v___x_472_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v___f_470_, v___x_471_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object* v_e_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3(lean_object* v_00_u03b1_480_, lean_object* v_x_481_, uint8_t v_isExporting_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(v_x_481_, v_isExporting_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___boxed(lean_object* v_00_u03b1_489_, lean_object* v_x_490_, lean_object* v_isExporting_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
uint8_t v_isExporting_boxed_497_; lean_object* v_res_498_; 
v_isExporting_boxed_497_ = lean_unbox(v_isExporting_491_);
v_res_498_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3(v_00_u03b1_489_, v_x_490_, v_isExporting_boxed_497_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object* v_00_u03b1_499_, lean_object* v_x_500_, uint8_t v_when_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_500_, v_when_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object* v_00_u03b1_508_, lean_object* v_x_509_, lean_object* v_when_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v_when_boxed_516_; lean_object* v_res_517_; 
v_when_boxed_516_ = lean_unbox(v_when_510_);
v_res_517_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(v_00_u03b1_508_, v_x_509_, v_when_boxed_516_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1(uint8_t v_a_518_, uint8_t v___x_519_, lean_object* v___x_520_, lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(v_a_518_, v___x_519_, v___x_520_, v_x_521_, v_x_522_, v_x_523_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___boxed(lean_object* v_a_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint8_t v_a_4672__boxed_541_; uint8_t v___x_4673__boxed_542_; lean_object* v_res_543_; 
v_a_4672__boxed_541_ = lean_unbox(v_a_530_);
v___x_4673__boxed_542_ = lean_unbox(v___x_531_);
v_res_543_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1(v_a_4672__boxed_541_, v___x_4673__boxed_542_, v___x_532_, v_x_533_, v_x_534_, v_x_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(lean_object* v_x_544_, uint8_t v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_box(v___y_545_);
lean_inc(v___y_546_);
v___x_553_ = lean_apply_7(v_x_544_, v___x_552_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, lean_box(0));
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed(lean_object* v_x_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v___y_26151__boxed_562_; lean_object* v_res_563_; 
v___y_26151__boxed_562_ = lean_unbox(v___y_555_);
v_res_563_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(v_x_554_, v___y_26151__boxed_562_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_556_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object* v_lctx_564_, lean_object* v_localInsts_565_, lean_object* v_x_566_, uint8_t v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v___f_575_; lean_object* v___x_576_; 
v___x_574_ = lean_box(v___y_567_);
lean_inc(v___y_568_);
v___f_575_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_575_, 0, v_x_566_);
lean_closure_set(v___f_575_, 1, v___x_574_);
lean_closure_set(v___f_575_, 2, v___y_568_);
v___x_576_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_564_, v_localInsts_565_, v___f_575_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_576_) == 0)
{
return v___x_576_;
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___boxed(lean_object* v_lctx_585_, lean_object* v_localInsts_586_, lean_object* v_x_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
uint8_t v___y_26176__boxed_595_; lean_object* v_res_596_; 
v___y_26176__boxed_595_ = lean_unbox(v___y_588_);
v_res_596_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_lctx_585_, v_localInsts_586_, v_x_587_, v___y_26176__boxed_595_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object* v_00_u03b1_597_, lean_object* v_lctx_598_, lean_object* v_localInsts_599_, lean_object* v_x_600_, uint8_t v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_lctx_598_, v_localInsts_599_, v_x_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object* v_00_u03b1_609_, lean_object* v_lctx_610_, lean_object* v_localInsts_611_, lean_object* v_x_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
uint8_t v___y_26220__boxed_620_; lean_object* v_res_621_; 
v___y_26220__boxed_620_ = lean_unbox(v___y_613_);
v_res_621_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_00_u03b1_609_, v_lctx_610_, v_localInsts_611_, v_x_612_, v___y_26220__boxed_620_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(lean_object* v_k_622_, uint8_t v___y_623_, lean_object* v___y_624_, lean_object* v_b_625_, lean_object* v_c_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_box(v___y_623_);
lean_inc(v___y_630_);
lean_inc_ref(v___y_629_);
lean_inc(v___y_628_);
lean_inc_ref(v___y_627_);
lean_inc(v___y_624_);
v___x_633_ = lean_apply_9(v_k_622_, v_b_625_, v_c_626_, v___x_632_, v___y_624_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, lean_box(0));
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed(lean_object* v_k_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v_b_637_, lean_object* v_c_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
uint8_t v___y_26243__boxed_644_; lean_object* v_res_645_; 
v___y_26243__boxed_644_ = lean_unbox(v___y_635_);
v_res_645_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(v_k_634_, v___y_26243__boxed_644_, v___y_636_, v_b_637_, v_c_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_636_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object* v_e_646_, lean_object* v_k_647_, uint8_t v_cleanupAnnotations_648_, uint8_t v_preserveNondepLet_649_, uint8_t v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; lean_object* v___f_658_; uint8_t v___x_659_; uint8_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_657_ = lean_box(v___y_650_);
lean_inc(v___y_651_);
v___f_658_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_658_, 0, v_k_647_);
lean_closure_set(v___f_658_, 1, v___x_657_);
lean_closure_set(v___f_658_, 2, v___y_651_);
v___x_659_ = 1;
v___x_660_ = 0;
v___x_661_ = lean_box(0);
v___x_662_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_646_, v___x_659_, v___x_659_, v_preserveNondepLet_649_, v___x_660_, v___x_661_, v___f_658_, v_cleanupAnnotations_648_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_662_) == 0)
{
return v___x_662_;
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object* v_e_671_, lean_object* v_k_672_, lean_object* v_cleanupAnnotations_673_, lean_object* v_preserveNondepLet_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_682_; uint8_t v_preserveNondepLet_boxed_683_; uint8_t v___y_26268__boxed_684_; lean_object* v_res_685_; 
v_cleanupAnnotations_boxed_682_ = lean_unbox(v_cleanupAnnotations_673_);
v_preserveNondepLet_boxed_683_ = lean_unbox(v_preserveNondepLet_674_);
v___y_26268__boxed_684_ = lean_unbox(v___y_675_);
v_res_685_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_671_, v_k_672_, v_cleanupAnnotations_boxed_682_, v_preserveNondepLet_boxed_683_, v___y_26268__boxed_684_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object* v_00_u03b1_686_, lean_object* v_e_687_, lean_object* v_k_688_, uint8_t v_cleanupAnnotations_689_, uint8_t v_preserveNondepLet_690_, uint8_t v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_687_, v_k_688_, v_cleanupAnnotations_689_, v_preserveNondepLet_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object* v_00_u03b1_699_, lean_object* v_e_700_, lean_object* v_k_701_, lean_object* v_cleanupAnnotations_702_, lean_object* v_preserveNondepLet_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_711_; uint8_t v_preserveNondepLet_boxed_712_; uint8_t v___y_26318__boxed_713_; lean_object* v_res_714_; 
v_cleanupAnnotations_boxed_711_ = lean_unbox(v_cleanupAnnotations_702_);
v_preserveNondepLet_boxed_712_ = lean_unbox(v_preserveNondepLet_703_);
v___y_26318__boxed_713_ = lean_unbox(v___y_704_);
v_res_714_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(v_00_u03b1_699_, v_e_700_, v_k_701_, v_cleanupAnnotations_boxed_711_, v_preserveNondepLet_boxed_712_, v___y_26318__boxed_713_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(lean_object* v_type_715_, lean_object* v_k_716_, uint8_t v_cleanupAnnotations_717_, uint8_t v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___f_726_; uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_725_ = lean_box(v___y_718_);
lean_inc(v___y_719_);
v___f_726_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_726_, 0, v_k_716_);
lean_closure_set(v___f_726_, 1, v___x_725_);
lean_closure_set(v___f_726_, 2, v___y_719_);
v___x_727_ = 0;
v___x_728_ = lean_box(0);
v___x_729_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_727_, v___x_728_, v_type_715_, v___f_726_, v_cleanupAnnotations_717_, v___x_727_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_729_) == 0)
{
return v___x_729_;
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___boxed(lean_object* v_type_738_, lean_object* v_k_739_, lean_object* v_cleanupAnnotations_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_748_; uint8_t v___y_26341__boxed_749_; lean_object* v_res_750_; 
v_cleanupAnnotations_boxed_748_ = lean_unbox(v_cleanupAnnotations_740_);
v___y_26341__boxed_749_ = lean_unbox(v___y_741_);
v_res_750_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_738_, v_k_739_, v_cleanupAnnotations_boxed_748_, v___y_26341__boxed_749_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object* v_00_u03b1_751_, lean_object* v_type_752_, lean_object* v_k_753_, uint8_t v_cleanupAnnotations_754_, uint8_t v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_752_, v_k_753_, v_cleanupAnnotations_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object* v_00_u03b1_763_, lean_object* v_type_764_, lean_object* v_k_765_, lean_object* v_cleanupAnnotations_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_774_; uint8_t v___y_26389__boxed_775_; lean_object* v_res_776_; 
v_cleanupAnnotations_boxed_774_ = lean_unbox(v_cleanupAnnotations_766_);
v___y_26389__boxed_775_ = lean_unbox(v___y_767_);
v_res_776_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_00_u03b1_763_, v_type_764_, v_k_765_, v_cleanupAnnotations_boxed_774_, v___y_26389__boxed_775_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
lean_object* v_ks_781_; lean_object* v_vs_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_806_; 
v_ks_781_ = lean_ctor_get(v_x_777_, 0);
v_vs_782_ = lean_ctor_get(v_x_777_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_806_ == 0)
{
v___x_784_ = v_x_777_;
v_isShared_785_ = v_isSharedCheck_806_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_vs_782_);
lean_inc(v_ks_781_);
lean_dec(v_x_777_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_806_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = lean_array_get_size(v_ks_781_);
v___x_787_ = lean_nat_dec_lt(v_x_778_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
lean_dec(v_x_778_);
v___x_788_ = lean_array_push(v_ks_781_, v_x_779_);
v___x_789_ = lean_array_push(v_vs_782_, v_x_780_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_789_);
lean_ctor_set(v___x_784_, 0, v___x_788_);
v___x_791_ = v___x_784_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
else
{
lean_object* v_k_x27_793_; uint8_t v___x_794_; 
v_k_x27_793_ = lean_array_fget_borrowed(v_ks_781_, v_x_778_);
v___x_794_ = l_Lean_instBEqFVarId_beq(v_x_779_, v_k_x27_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_796_; 
if (v_isShared_785_ == 0)
{
v___x_796_ = v___x_784_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_ks_781_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_vs_782_);
v___x_796_ = v_reuseFailAlloc_800_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(1u);
v___x_798_ = lean_nat_add(v_x_778_, v___x_797_);
lean_dec(v_x_778_);
v_x_777_ = v___x_796_;
v_x_778_ = v___x_798_;
goto _start;
}
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_801_ = lean_array_fset(v_ks_781_, v_x_778_, v_x_779_);
v___x_802_ = lean_array_fset(v_vs_782_, v_x_778_, v_x_780_);
lean_dec(v_x_778_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_802_);
lean_ctor_set(v___x_784_, 0, v___x_801_);
v___x_804_ = v___x_784_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_802_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(lean_object* v_n_807_, lean_object* v_k_808_, lean_object* v_v_809_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(v_n_807_, v___x_810_, v_k_808_, v_v_809_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object* v_x_813_, size_t v_x_814_, size_t v_x_815_, lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
if (lean_obj_tag(v_x_813_) == 0)
{
lean_object* v_es_818_; size_t v___x_819_; size_t v___x_820_; lean_object* v_j_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v_es_818_ = lean_ctor_get(v_x_813_, 0);
v___x_819_ = ((size_t)31ULL);
v___x_820_ = lean_usize_land(v_x_814_, v___x_819_);
v_j_821_ = lean_usize_to_nat(v___x_820_);
v___x_822_ = lean_array_get_size(v_es_818_);
v___x_823_ = lean_nat_dec_lt(v_j_821_, v___x_822_);
if (v___x_823_ == 0)
{
lean_dec(v_j_821_);
lean_dec(v_x_817_);
lean_dec(v_x_816_);
return v_x_813_;
}
else
{
lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_862_; 
lean_inc_ref(v_es_818_);
v_isSharedCheck_862_ = !lean_is_exclusive(v_x_813_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; 
v_unused_863_ = lean_ctor_get(v_x_813_, 0);
lean_dec(v_unused_863_);
v___x_825_ = v_x_813_;
v_isShared_826_ = v_isSharedCheck_862_;
goto v_resetjp_824_;
}
else
{
lean_dec(v_x_813_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_862_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_v_827_; lean_object* v___x_828_; lean_object* v_xs_x27_829_; lean_object* v___y_831_; 
v_v_827_ = lean_array_fget(v_es_818_, v_j_821_);
v___x_828_ = lean_box(0);
v_xs_x27_829_ = lean_array_fset(v_es_818_, v_j_821_, v___x_828_);
switch(lean_obj_tag(v_v_827_))
{
case 0:
{
lean_object* v_key_836_; lean_object* v_val_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_847_; 
v_key_836_ = lean_ctor_get(v_v_827_, 0);
v_val_837_ = lean_ctor_get(v_v_827_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v_v_827_);
if (v_isSharedCheck_847_ == 0)
{
v___x_839_ = v_v_827_;
v_isShared_840_ = v_isSharedCheck_847_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_val_837_);
lean_inc(v_key_836_);
lean_dec(v_v_827_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_847_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_instBEqFVarId_beq(v_x_816_, v_key_836_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_del_object(v___x_839_);
v___x_842_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_836_, v_val_837_, v_x_816_, v_x_817_);
v___x_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
v___y_831_ = v___x_843_;
goto v___jp_830_;
}
else
{
lean_object* v___x_845_; 
lean_dec(v_val_837_);
lean_dec(v_key_836_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v_x_817_);
lean_ctor_set(v___x_839_, 0, v_x_816_);
v___x_845_ = v___x_839_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_x_816_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_x_817_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
v___y_831_ = v___x_845_;
goto v___jp_830_;
}
}
}
}
case 1:
{
lean_object* v_node_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_860_; 
v_node_848_ = lean_ctor_get(v_v_827_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_v_827_);
if (v_isSharedCheck_860_ == 0)
{
v___x_850_ = v_v_827_;
v_isShared_851_ = v_isSharedCheck_860_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_node_848_);
lean_dec(v_v_827_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_860_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
size_t v___x_852_; size_t v___x_853_; size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_852_ = ((size_t)5ULL);
v___x_853_ = lean_usize_shift_right(v_x_814_, v___x_852_);
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_add(v_x_815_, v___x_854_);
v___x_856_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_node_848_, v___x_853_, v___x_855_, v_x_816_, v_x_817_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_856_);
v___x_858_ = v___x_850_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
v___y_831_ = v___x_858_;
goto v___jp_830_;
}
}
}
default: 
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_x_816_);
lean_ctor_set(v___x_861_, 1, v_x_817_);
v___y_831_ = v___x_861_;
goto v___jp_830_;
}
}
v___jp_830_:
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = lean_array_fset(v_xs_x27_829_, v_j_821_, v___y_831_);
lean_dec(v_j_821_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_832_);
v___x_834_ = v___x_825_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
else
{
lean_object* v_ks_864_; lean_object* v_vs_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_883_; 
v_ks_864_ = lean_ctor_get(v_x_813_, 0);
v_vs_865_ = lean_ctor_get(v_x_813_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_x_813_);
if (v_isSharedCheck_883_ == 0)
{
v___x_867_ = v_x_813_;
v_isShared_868_ = v_isSharedCheck_883_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_vs_865_);
lean_inc(v_ks_864_);
lean_dec(v_x_813_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_883_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_ks_864_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_vs_865_);
v___x_870_ = v_reuseFailAlloc_882_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v_newNode_871_; size_t v___x_872_; uint8_t v___x_873_; 
v_newNode_871_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(v___x_870_, v_x_816_, v_x_817_);
v___x_872_ = ((size_t)7ULL);
v___x_873_ = lean_usize_dec_le(v___x_872_, v_x_815_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_874_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_871_);
v___x_875_ = lean_unsigned_to_nat(4u);
v___x_876_ = lean_nat_dec_lt(v___x_874_, v___x_875_);
lean_dec(v___x_874_);
if (v___x_876_ == 0)
{
lean_object* v_ks_877_; lean_object* v_vs_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_ks_877_ = lean_ctor_get(v_newNode_871_, 0);
lean_inc_ref(v_ks_877_);
v_vs_878_ = lean_ctor_get(v_newNode_871_, 1);
lean_inc_ref(v_vs_878_);
lean_dec_ref(v_newNode_871_);
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0);
v___x_881_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_x_815_, v_ks_877_, v_vs_878_, v___x_879_, v___x_880_);
lean_dec_ref(v_vs_878_);
lean_dec_ref(v_ks_877_);
return v___x_881_;
}
else
{
return v_newNode_871_;
}
}
else
{
return v_newNode_871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(size_t v_depth_884_, lean_object* v_keys_885_, lean_object* v_vals_886_, lean_object* v_i_887_, lean_object* v_entries_888_){
_start:
{
lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_889_ = lean_array_get_size(v_keys_885_);
v___x_890_ = lean_nat_dec_lt(v_i_887_, v___x_889_);
if (v___x_890_ == 0)
{
lean_dec(v_i_887_);
return v_entries_888_;
}
else
{
lean_object* v_k_891_; lean_object* v_v_892_; uint64_t v___x_893_; size_t v_h_894_; size_t v___x_895_; lean_object* v___x_896_; size_t v___x_897_; size_t v___x_898_; size_t v___x_899_; size_t v_h_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_k_891_ = lean_array_fget_borrowed(v_keys_885_, v_i_887_);
v_v_892_ = lean_array_fget_borrowed(v_vals_886_, v_i_887_);
v___x_893_ = l_Lean_instHashableFVarId_hash(v_k_891_);
v_h_894_ = lean_uint64_to_usize(v___x_893_);
v___x_895_ = ((size_t)5ULL);
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_sub(v_depth_884_, v___x_897_);
v___x_899_ = lean_usize_mul(v___x_895_, v___x_898_);
v_h_900_ = lean_usize_shift_right(v_h_894_, v___x_899_);
v___x_901_ = lean_nat_add(v_i_887_, v___x_896_);
lean_dec(v_i_887_);
lean_inc(v_v_892_);
lean_inc(v_k_891_);
v___x_902_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_entries_888_, v_h_900_, v_depth_884_, v_k_891_, v_v_892_);
v_i_887_ = v___x_901_;
v_entries_888_ = v___x_902_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_depth_904_, lean_object* v_keys_905_, lean_object* v_vals_906_, lean_object* v_i_907_, lean_object* v_entries_908_){
_start:
{
size_t v_depth_boxed_909_; lean_object* v_res_910_; 
v_depth_boxed_909_ = lean_unbox_usize(v_depth_904_);
lean_dec(v_depth_904_);
v_res_910_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_depth_boxed_909_, v_keys_905_, v_vals_906_, v_i_907_, v_entries_908_);
lean_dec_ref(v_vals_906_);
lean_dec_ref(v_keys_905_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
size_t v_x_26489__boxed_916_; size_t v_x_26490__boxed_917_; lean_object* v_res_918_; 
v_x_26489__boxed_916_ = lean_unbox_usize(v_x_912_);
lean_dec(v_x_912_);
v_x_26490__boxed_917_ = lean_unbox_usize(v_x_913_);
lean_dec(v_x_913_);
v_res_918_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_911_, v_x_26489__boxed_916_, v_x_26490__boxed_917_, v_x_914_, v_x_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object* v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
uint64_t v___x_922_; size_t v___x_923_; size_t v___x_924_; lean_object* v___x_925_; 
v___x_922_ = l_Lean_instHashableFVarId_hash(v_x_920_);
v___x_923_ = lean_uint64_to_usize(v___x_922_);
v___x_924_ = ((size_t)1ULL);
v___x_925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_919_, v___x_923_, v___x_924_, v_x_920_, v_x_921_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(lean_object* v_a_926_, lean_object* v_b_927_, lean_object* v_x_928_){
_start:
{
if (lean_obj_tag(v_x_928_) == 0)
{
lean_dec(v_b_927_);
lean_dec_ref(v_a_926_);
return v_x_928_;
}
else
{
lean_object* v_key_929_; lean_object* v_value_930_; lean_object* v_tail_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_943_; 
v_key_929_ = lean_ctor_get(v_x_928_, 0);
v_value_930_ = lean_ctor_get(v_x_928_, 1);
v_tail_931_ = lean_ctor_get(v_x_928_, 2);
v_isSharedCheck_943_ = !lean_is_exclusive(v_x_928_);
if (v_isSharedCheck_943_ == 0)
{
v___x_933_ = v_x_928_;
v_isShared_934_ = v_isSharedCheck_943_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_tail_931_);
lean_inc(v_value_930_);
lean_inc(v_key_929_);
lean_dec(v_x_928_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_943_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
uint8_t v___x_935_; 
v___x_935_ = l_Lean_ExprStructEq_beq(v_key_929_, v_a_926_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_926_, v_b_927_, v_tail_931_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 2, v___x_936_);
v___x_938_ = v___x_933_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_key_929_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_value_930_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_object* v___x_941_; 
lean_dec(v_value_930_);
lean_dec(v_key_929_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v_b_927_);
lean_ctor_set(v___x_933_, 0, v_a_926_);
v___x_941_ = v___x_933_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_926_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_b_927_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_tail_931_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(lean_object* v_a_944_, lean_object* v_x_945_){
_start:
{
if (lean_obj_tag(v_x_945_) == 0)
{
uint8_t v___x_946_; 
v___x_946_ = 0;
return v___x_946_;
}
else
{
lean_object* v_key_947_; lean_object* v_tail_948_; uint8_t v___x_949_; 
v_key_947_ = lean_ctor_get(v_x_945_, 0);
v_tail_948_ = lean_ctor_get(v_x_945_, 2);
v___x_949_ = l_Lean_ExprStructEq_beq(v_key_947_, v_a_944_);
if (v___x_949_ == 0)
{
v_x_945_ = v_tail_948_;
goto _start;
}
else
{
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg___boxed(lean_object* v_a_951_, lean_object* v_x_952_){
_start:
{
uint8_t v_res_953_; lean_object* v_r_954_; 
v_res_953_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_951_, v_x_952_);
lean_dec(v_x_952_);
lean_dec_ref(v_a_951_);
v_r_954_ = lean_box(v_res_953_);
return v_r_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(lean_object* v_x_955_, lean_object* v_x_956_){
_start:
{
if (lean_obj_tag(v_x_956_) == 0)
{
return v_x_955_;
}
else
{
lean_object* v_key_957_; lean_object* v_value_958_; lean_object* v_tail_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_982_; 
v_key_957_ = lean_ctor_get(v_x_956_, 0);
v_value_958_ = lean_ctor_get(v_x_956_, 1);
v_tail_959_ = lean_ctor_get(v_x_956_, 2);
v_isSharedCheck_982_ = !lean_is_exclusive(v_x_956_);
if (v_isSharedCheck_982_ == 0)
{
v___x_961_ = v_x_956_;
v_isShared_962_ = v_isSharedCheck_982_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_tail_959_);
lean_inc(v_value_958_);
lean_inc(v_key_957_);
lean_dec(v_x_956_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_982_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; uint64_t v___x_964_; uint64_t v___x_965_; uint64_t v___x_966_; uint64_t v_fold_967_; uint64_t v___x_968_; uint64_t v___x_969_; uint64_t v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v___x_973_; size_t v___x_974_; size_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_963_ = lean_array_get_size(v_x_955_);
v___x_964_ = l_Lean_ExprStructEq_hash(v_key_957_);
v___x_965_ = 32ULL;
v___x_966_ = lean_uint64_shift_right(v___x_964_, v___x_965_);
v_fold_967_ = lean_uint64_xor(v___x_964_, v___x_966_);
v___x_968_ = 16ULL;
v___x_969_ = lean_uint64_shift_right(v_fold_967_, v___x_968_);
v___x_970_ = lean_uint64_xor(v_fold_967_, v___x_969_);
v___x_971_ = lean_uint64_to_usize(v___x_970_);
v___x_972_ = lean_usize_of_nat(v___x_963_);
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_sub(v___x_972_, v___x_973_);
v___x_975_ = lean_usize_land(v___x_971_, v___x_974_);
v___x_976_ = lean_array_uget_borrowed(v_x_955_, v___x_975_);
lean_inc(v___x_976_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 2, v___x_976_);
v___x_978_ = v___x_961_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_key_957_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_value_958_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v___x_976_);
v___x_978_ = v_reuseFailAlloc_981_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; 
v___x_979_ = lean_array_uset(v_x_955_, v___x_975_, v___x_978_);
v_x_955_ = v___x_979_;
v_x_956_ = v_tail_959_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(lean_object* v_i_983_, lean_object* v_source_984_, lean_object* v_target_985_){
_start:
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_array_get_size(v_source_984_);
v___x_987_ = lean_nat_dec_lt(v_i_983_, v___x_986_);
if (v___x_987_ == 0)
{
lean_dec_ref(v_source_984_);
lean_dec(v_i_983_);
return v_target_985_;
}
else
{
lean_object* v_es_988_; lean_object* v___x_989_; lean_object* v_source_990_; lean_object* v_target_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_es_988_ = lean_array_fget(v_source_984_, v_i_983_);
v___x_989_ = lean_box(0);
v_source_990_ = lean_array_fset(v_source_984_, v_i_983_, v___x_989_);
v_target_991_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(v_target_985_, v_es_988_);
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = lean_nat_add(v_i_983_, v___x_992_);
lean_dec(v_i_983_);
v_i_983_ = v___x_993_;
v_source_984_ = v_source_990_;
v_target_985_ = v_target_991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(lean_object* v_data_995_){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_nbuckets_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_996_ = lean_array_get_size(v_data_995_);
v___x_997_ = lean_unsigned_to_nat(2u);
v_nbuckets_998_ = lean_nat_mul(v___x_996_, v___x_997_);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_mk_array(v_nbuckets_998_, v___x_1000_);
v___x_1002_ = lean_array_propagate_mark(v_data_995_, v___x_1001_);
v___x_1003_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(v___x_999_, v_data_995_, v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(lean_object* v_m_1004_, lean_object* v_a_1005_, lean_object* v_b_1006_){
_start:
{
lean_object* v_size_1007_; lean_object* v_buckets_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1051_; 
v_size_1007_ = lean_ctor_get(v_m_1004_, 0);
v_buckets_1008_ = lean_ctor_get(v_m_1004_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_m_1004_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1010_ = v_m_1004_;
v_isShared_1011_ = v_isSharedCheck_1051_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_buckets_1008_);
lean_inc(v_size_1007_);
lean_dec(v_m_1004_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1051_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; uint64_t v___x_1013_; uint64_t v___x_1014_; uint64_t v___x_1015_; uint64_t v_fold_1016_; uint64_t v___x_1017_; uint64_t v___x_1018_; uint64_t v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; size_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; lean_object* v_bkt_1025_; uint8_t v___x_1026_; 
v___x_1012_ = lean_array_get_size(v_buckets_1008_);
v___x_1013_ = l_Lean_ExprStructEq_hash(v_a_1005_);
v___x_1014_ = 32ULL;
v___x_1015_ = lean_uint64_shift_right(v___x_1013_, v___x_1014_);
v_fold_1016_ = lean_uint64_xor(v___x_1013_, v___x_1015_);
v___x_1017_ = 16ULL;
v___x_1018_ = lean_uint64_shift_right(v_fold_1016_, v___x_1017_);
v___x_1019_ = lean_uint64_xor(v_fold_1016_, v___x_1018_);
v___x_1020_ = lean_uint64_to_usize(v___x_1019_);
v___x_1021_ = lean_usize_of_nat(v___x_1012_);
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_sub(v___x_1021_, v___x_1022_);
v___x_1024_ = lean_usize_land(v___x_1020_, v___x_1023_);
v_bkt_1025_ = lean_array_uget_borrowed(v_buckets_1008_, v___x_1024_);
v___x_1026_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_1005_, v_bkt_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v_size_x27_1028_; lean_object* v___x_1029_; lean_object* v_buckets_x27_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1027_ = lean_unsigned_to_nat(1u);
v_size_x27_1028_ = lean_nat_add(v_size_1007_, v___x_1027_);
lean_dec(v_size_1007_);
lean_inc(v_bkt_1025_);
v___x_1029_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1029_, 0, v_a_1005_);
lean_ctor_set(v___x_1029_, 1, v_b_1006_);
lean_ctor_set(v___x_1029_, 2, v_bkt_1025_);
v_buckets_x27_1030_ = lean_array_uset(v_buckets_1008_, v___x_1024_, v___x_1029_);
v___x_1031_ = lean_unsigned_to_nat(4u);
v___x_1032_ = lean_nat_mul(v_size_x27_1028_, v___x_1031_);
v___x_1033_ = lean_unsigned_to_nat(3u);
v___x_1034_ = lean_nat_div(v___x_1032_, v___x_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_array_get_size(v_buckets_x27_1030_);
v___x_1036_ = lean_nat_dec_le(v___x_1034_, v___x_1035_);
lean_dec(v___x_1034_);
if (v___x_1036_ == 0)
{
lean_object* v_val_1037_; lean_object* v___x_1039_; 
v_val_1037_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(v_buckets_x27_1030_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 1, v_val_1037_);
lean_ctor_set(v___x_1010_, 0, v_size_x27_1028_);
v___x_1039_ = v___x_1010_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_size_x27_1028_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_val_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
else
{
lean_object* v___x_1042_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 1, v_buckets_x27_1030_);
lean_ctor_set(v___x_1010_, 0, v_size_x27_1028_);
v___x_1042_ = v___x_1010_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_size_x27_1028_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_buckets_x27_1030_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
lean_object* v___x_1044_; lean_object* v_buckets_x27_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
lean_inc(v_bkt_1025_);
v___x_1044_ = lean_box(0);
v_buckets_x27_1045_ = lean_array_uset(v_buckets_1008_, v___x_1024_, v___x_1044_);
v___x_1046_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_1005_, v_b_1006_, v_bkt_1025_);
v___x_1047_ = lean_array_uset(v_buckets_x27_1045_, v___x_1024_, v___x_1046_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 1, v___x_1047_);
v___x_1049_ = v___x_1010_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_size_1007_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(lean_object* v_a_1052_, lean_object* v_x_1053_){
_start:
{
if (lean_obj_tag(v_x_1053_) == 0)
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_box(0);
return v___x_1054_;
}
else
{
lean_object* v_key_1055_; lean_object* v_value_1056_; lean_object* v_tail_1057_; uint8_t v___x_1058_; 
v_key_1055_ = lean_ctor_get(v_x_1053_, 0);
v_value_1056_ = lean_ctor_get(v_x_1053_, 1);
v_tail_1057_ = lean_ctor_get(v_x_1053_, 2);
v___x_1058_ = l_Lean_ExprStructEq_beq(v_key_1055_, v_a_1052_);
if (v___x_1058_ == 0)
{
v_x_1053_ = v_tail_1057_;
goto _start;
}
else
{
lean_object* v___x_1060_; 
lean_inc(v_value_1056_);
v___x_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1060_, 0, v_value_1056_);
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___boxed(lean_object* v_a_1061_, lean_object* v_x_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1061_, v_x_1062_);
lean_dec(v_x_1062_);
lean_dec_ref(v_a_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(lean_object* v_m_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_buckets_1066_; lean_object* v___x_1067_; uint64_t v___x_1068_; uint64_t v___x_1069_; uint64_t v___x_1070_; uint64_t v_fold_1071_; uint64_t v___x_1072_; uint64_t v___x_1073_; uint64_t v___x_1074_; size_t v___x_1075_; size_t v___x_1076_; size_t v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_buckets_1066_ = lean_ctor_get(v_m_1064_, 1);
v___x_1067_ = lean_array_get_size(v_buckets_1066_);
v___x_1068_ = l_Lean_ExprStructEq_hash(v_a_1065_);
v___x_1069_ = 32ULL;
v___x_1070_ = lean_uint64_shift_right(v___x_1068_, v___x_1069_);
v_fold_1071_ = lean_uint64_xor(v___x_1068_, v___x_1070_);
v___x_1072_ = 16ULL;
v___x_1073_ = lean_uint64_shift_right(v_fold_1071_, v___x_1072_);
v___x_1074_ = lean_uint64_xor(v_fold_1071_, v___x_1073_);
v___x_1075_ = lean_uint64_to_usize(v___x_1074_);
v___x_1076_ = lean_usize_of_nat(v___x_1067_);
v___x_1077_ = ((size_t)1ULL);
v___x_1078_ = lean_usize_sub(v___x_1076_, v___x_1077_);
v___x_1079_ = lean_usize_land(v___x_1075_, v___x_1078_);
v___x_1080_ = lean_array_uget_borrowed(v_buckets_1066_, v___x_1079_);
v___x_1081_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1065_, v___x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___boxed(lean_object* v_m_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_m_1082_, v_a_1083_);
lean_dec_ref(v_a_1083_);
lean_dec_ref(v_m_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0(lean_object* v_proof_1085_, uint8_t v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; 
lean_inc(v___y_1091_);
lean_inc_ref(v___y_1090_);
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1088_);
v___x_1093_ = lean_infer_type(v_proof_1085_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0___boxed(lean_object* v_proof_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v___y_26908__boxed_1102_; lean_object* v_res_1103_; 
v___y_26908__boxed_1102_ = lean_unbox(v___y_1095_);
v_res_1103_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0(v_proof_1094_, v___y_26908__boxed_1102_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(lean_object* v_x_1104_, uint8_t v_isExporting_1105_, uint8_t v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v_env_1114_; lean_object* v___x_1115_; uint8_t v_isModule_1116_; 
v___x_1113_ = lean_st_ref_get(v___y_1111_);
v_env_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_env_1114_);
lean_dec(v___x_1113_);
v___x_1115_ = l_Lean_Environment_header(v_env_1114_);
v_isModule_1116_ = lean_ctor_get_uint8(v___x_1115_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1115_);
if (v_isModule_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec_ref(v_env_1114_);
v___x_1117_ = lean_box(v___y_1106_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v___y_1107_);
v___x_1118_ = lean_apply_7(v_x_1104_, v___x_1117_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, lean_box(0));
return v___x_1118_;
}
else
{
uint8_t v_isExporting_1119_; 
v_isExporting_1119_ = lean_ctor_get_uint8(v_env_1114_, sizeof(void*)*8);
lean_dec_ref(v_env_1114_);
if (v_isExporting_1105_ == 0)
{
if (v_isExporting_1119_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_box(v___y_1106_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v___y_1107_);
v___x_1188_ = lean_apply_7(v_x_1104_, v___x_1187_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, lean_box(0));
return v___x_1188_;
}
else
{
goto v___jp_1120_;
}
}
else
{
if (v_isExporting_1119_ == 0)
{
goto v___jp_1120_;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_box(v___y_1106_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v___y_1107_);
v___x_1190_ = lean_apply_7(v_x_1104_, v___x_1189_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, lean_box(0));
return v___x_1190_;
}
}
v___jp_1120_:
{
lean_object* v___x_1121_; lean_object* v_env_1122_; lean_object* v_nextMacroScope_1123_; lean_object* v_ngen_1124_; lean_object* v_auxDeclNGen_1125_; lean_object* v_traceState_1126_; lean_object* v_recordedDeps_1127_; lean_object* v_messages_1128_; lean_object* v_infoState_1129_; lean_object* v_snapshotTasks_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1185_; 
v___x_1121_ = lean_st_ref_take(v___y_1111_);
v_env_1122_ = lean_ctor_get(v___x_1121_, 0);
v_nextMacroScope_1123_ = lean_ctor_get(v___x_1121_, 1);
v_ngen_1124_ = lean_ctor_get(v___x_1121_, 2);
v_auxDeclNGen_1125_ = lean_ctor_get(v___x_1121_, 3);
v_traceState_1126_ = lean_ctor_get(v___x_1121_, 4);
v_recordedDeps_1127_ = lean_ctor_get(v___x_1121_, 6);
v_messages_1128_ = lean_ctor_get(v___x_1121_, 7);
v_infoState_1129_ = lean_ctor_get(v___x_1121_, 8);
v_snapshotTasks_1130_ = lean_ctor_get(v___x_1121_, 9);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; 
v_unused_1186_ = lean_ctor_get(v___x_1121_, 5);
lean_dec(v_unused_1186_);
v___x_1132_ = v___x_1121_;
v_isShared_1133_ = v_isSharedCheck_1185_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_snapshotTasks_1130_);
lean_inc(v_infoState_1129_);
lean_inc(v_messages_1128_);
lean_inc(v_recordedDeps_1127_);
lean_inc(v_traceState_1126_);
lean_inc(v_auxDeclNGen_1125_);
lean_inc(v_ngen_1124_);
lean_inc(v_nextMacroScope_1123_);
lean_inc(v_env_1122_);
lean_dec(v___x_1121_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1185_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1134_ = l_Lean_Environment_setExporting(v_env_1122_, v_isExporting_1105_);
v___x_1135_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 5, v___x_1135_);
lean_ctor_set(v___x_1132_, 0, v___x_1134_);
v___x_1137_ = v___x_1132_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_nextMacroScope_1123_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_ngen_1124_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_auxDeclNGen_1125_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v_traceState_1126_);
lean_ctor_set(v_reuseFailAlloc_1184_, 5, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1184_, 6, v_recordedDeps_1127_);
lean_ctor_set(v_reuseFailAlloc_1184_, 7, v_messages_1128_);
lean_ctor_set(v_reuseFailAlloc_1184_, 8, v_infoState_1129_);
lean_ctor_set(v_reuseFailAlloc_1184_, 9, v_snapshotTasks_1130_);
v___x_1137_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_mctx_1140_; lean_object* v_zetaDeltaFVarIds_1141_; lean_object* v_postponed_1142_; lean_object* v_diag_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1182_; 
v___x_1138_ = lean_st_ref_put(v___y_1111_, v___x_1137_);
v___x_1139_ = lean_st_ref_take(v___y_1109_);
v_mctx_1140_ = lean_ctor_get(v___x_1139_, 0);
v_zetaDeltaFVarIds_1141_ = lean_ctor_get(v___x_1139_, 2);
v_postponed_1142_ = lean_ctor_get(v___x_1139_, 3);
v_diag_1143_ = lean_ctor_get(v___x_1139_, 4);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v___x_1139_, 1);
lean_dec(v_unused_1183_);
v___x_1145_ = v___x_1139_;
v_isShared_1146_ = v_isSharedCheck_1182_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_diag_1143_);
lean_inc(v_postponed_1142_);
lean_inc(v_zetaDeltaFVarIds_1141_);
lean_inc(v_mctx_1140_);
lean_dec(v___x_1139_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1182_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_mctx_1140_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_zetaDeltaFVarIds_1141_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v_postponed_1142_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v_diag_1143_);
v___x_1149_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_r_1152_; 
v___x_1150_ = lean_st_ref_put(v___y_1109_, v___x_1149_);
v___x_1151_ = lean_box(v___y_1106_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v___y_1107_);
v_r_1152_ = lean_apply_7(v_x_1104_, v___x_1151_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, lean_box(0));
if (lean_obj_tag(v_r_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1169_; 
v_a_1153_ = lean_ctor_get(v_r_1152_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_r_1152_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1155_ = v_r_1152_;
v_isShared_1156_ = v_isSharedCheck_1169_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v_r_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1169_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
lean_inc(v_a_1153_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set_tag(v___x_1155_, 1);
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v___x_1159_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_1111_, v_isExporting_1119_, v___x_1135_, v___y_1109_, v___x_1147_, v___x_1158_);
lean_dec_ref(v___x_1158_);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; 
v_unused_1167_ = lean_ctor_get(v___x_1159_, 0);
lean_dec(v_unused_1167_);
v___x_1161_ = v___x_1159_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_dec(v___x_1159_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v_a_1153_);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1153_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
v_a_1170_ = lean_ctor_get(v_r_1152_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v_r_1152_, 1);
v___x_1171_ = lean_box(0);
v___x_1172_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_1111_, v_isExporting_1119_, v___x_1135_, v___y_1109_, v___x_1147_, v___x_1171_);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; 
v_unused_1180_ = lean_ctor_get(v___x_1172_, 0);
lean_dec(v_unused_1180_);
v___x_1174_ = v___x_1172_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_dec(v___x_1172_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set_tag(v___x_1174_, 1);
lean_ctor_set(v___x_1174_, 0, v_a_1170_);
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1170_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg___boxed(lean_object* v_x_1191_, lean_object* v_isExporting_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v_isExporting_boxed_1200_; uint8_t v___y_26944__boxed_1201_; lean_object* v_res_1202_; 
v_isExporting_boxed_1200_ = lean_unbox(v_isExporting_1192_);
v___y_26944__boxed_1201_ = lean_unbox(v___y_1193_);
v_res_1202_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(v_x_1191_, v_isExporting_boxed_1200_, v___y_26944__boxed_1201_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(lean_object* v_x_1203_, uint8_t v_when_1204_, uint8_t v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
if (v_when_1204_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_box(v___y_1205_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
lean_inc(v___y_1208_);
lean_inc_ref(v___y_1207_);
lean_inc(v___y_1206_);
v___x_1213_ = lean_apply_7(v_x_1203_, v___x_1212_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, lean_box(0));
return v___x_1213_;
}
else
{
uint8_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = 0;
v___x_1215_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(v_x_1203_, v___x_1214_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg___boxed(lean_object* v_x_1216_, lean_object* v_when_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
uint8_t v_when_boxed_1225_; uint8_t v___y_27093__boxed_1226_; lean_object* v_res_1227_; 
v_when_boxed_1225_ = lean_unbox(v_when_1217_);
v___y_27093__boxed_1226_ = lean_unbox(v___y_1218_);
v_res_1227_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(v_x_1216_, v_when_boxed_1225_, v___y_27093__boxed_1226_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object* v_proof_1228_, uint8_t v_cache_1229_, lean_object* v_postprocessType_1230_, uint8_t v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___f_1238_; uint8_t v___x_1239_; lean_object* v___x_1240_; 
lean_inc_ref(v_proof_1228_);
v___f_1238_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1238_, 0, v_proof_1228_);
v___x_1239_ = 1;
v___x_1240_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(v___f_1238_, v___x_1239_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1242_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___x_1240_, 1);
v___x_1242_ = l_Lean_Core_betaReduce(v_a_1241_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1244_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v___x_1244_ = l_Lean_Meta_zetaReduce(v_a_1243_, v___x_1239_, v___x_1239_, v___x_1239_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1246_ = lean_box(v___y_1231_);
lean_inc(v___y_1236_);
lean_inc_ref(v___y_1235_);
lean_inc(v___y_1234_);
lean_inc_ref(v___y_1233_);
lean_inc(v___y_1232_);
v___x_1247_ = lean_apply_8(v_postprocessType_1230_, v_a_1245_, v___x_1246_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, lean_box(0));
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; uint8_t v___y_1250_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
if (v_cache_1229_ == 0)
{
v___y_1250_ = v_cache_1229_;
goto v___jp_1249_;
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = l_Lean_Expr_hasSorry(v_proof_1228_);
if (v___x_1253_ == 0)
{
v___y_1250_ = v_cache_1229_;
goto v___jp_1249_;
}
else
{
uint8_t v___x_1254_; 
v___x_1254_ = 0;
v___y_1250_ = v___x_1254_;
goto v___jp_1249_;
}
}
v___jp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_box(0);
v___x_1252_ = l_Lean_Meta_mkAuxTheorem(v_a_1248_, v_proof_1228_, v___x_1239_, v___x_1251_, v___y_1250_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v___x_1252_;
}
}
else
{
lean_dec_ref(v_proof_1228_);
return v___x_1247_;
}
}
else
{
lean_dec_ref(v_postprocessType_1230_);
lean_dec_ref(v_proof_1228_);
return v___x_1244_;
}
}
else
{
lean_dec_ref(v_postprocessType_1230_);
lean_dec_ref(v_proof_1228_);
return v___x_1242_;
}
}
else
{
lean_dec_ref(v_postprocessType_1230_);
lean_dec_ref(v_proof_1228_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object* v_proof_1255_, lean_object* v_cache_1256_, lean_object* v_postprocessType_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v_cache_boxed_1265_; uint8_t v___y_27122__boxed_1266_; lean_object* v_res_1267_; 
v_cache_boxed_1265_ = lean_unbox(v_cache_1256_);
v___y_27122__boxed_1266_ = lean_unbox(v___y_1258_);
v_res_1267_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_proof_1255_, v_cache_boxed_1265_, v_postprocessType_1257_, v___y_27122__boxed_1266_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object* v_as_1268_, size_t v_sz_1269_, size_t v_i_1270_, lean_object* v_b_1271_, uint8_t v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_a_1280_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; uint8_t v___x_1293_; 
v___x_1293_ = lean_usize_dec_lt(v_i_1270_, v_sz_1269_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v_b_1271_);
return v___x_1294_;
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1296_; lean_object* v_localDecl_1298_; lean_object* v___x_1306_; 
v_a_1295_ = lean_array_uget_borrowed(v_as_1268_, v_i_1270_);
v___x_1296_ = l_Lean_Expr_fvarId_x21(v_a_1295_);
lean_inc(v___x_1296_);
v___x_1306_ = l_Lean_FVarId_getDecl___redArg(v___x_1296_, v___y_1274_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = l_Lean_LocalDecl_type(v_a_1307_);
v___x_1309_ = l_Lean_Meta_AbstractNestedProofs_visit(v___x_1308_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1311_ = l_Lean_LocalDecl_setType(v_a_1307_, v_a_1310_);
v___x_1312_ = l_Lean_LocalDecl_value_x3f(v___x_1311_, v___x_1293_);
if (lean_obj_tag(v___x_1312_) == 0)
{
v_localDecl_1298_ = v___x_1311_;
goto v___jp_1297_;
}
else
{
lean_object* v_val_1313_; lean_object* v___x_1314_; 
v_val_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1314_ = l_Lean_Meta_AbstractNestedProofs_visit(v_val_1313_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1316_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = l_Lean_LocalDecl_setValue(v___x_1311_, v_a_1315_);
v_localDecl_1298_ = v___x_1316_;
goto v___jp_1297_;
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v___x_1311_);
lean_dec(v___x_1296_);
lean_dec_ref(v_b_1271_);
v_a_1317_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1314_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1314_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_a_1307_);
lean_dec(v___x_1296_);
lean_dec_ref(v_b_1271_);
v_a_1325_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1309_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1309_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v___x_1296_);
lean_dec_ref(v_b_1271_);
v_a_1333_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1306_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1306_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
v___jp_1297_:
{
lean_object* v_fvarIdToDecl_1299_; lean_object* v_decls_1300_; lean_object* v_auxDeclToFullName_1301_; lean_object* v___x_1302_; 
v_fvarIdToDecl_1299_ = lean_ctor_get(v_b_1271_, 0);
v_decls_1300_ = lean_ctor_get(v_b_1271_, 1);
v_auxDeclToFullName_1301_ = lean_ctor_get(v_b_1271_, 2);
lean_inc_ref(v_b_1271_);
v___x_1302_ = lean_local_ctx_find(v_b_1271_, v___x_1296_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_dec_ref(v_localDecl_1298_);
v_a_1280_ = v_b_1271_;
goto v___jp_1279_;
}
else
{
lean_object* v_index_1303_; lean_object* v_fvarId_1304_; lean_object* v___x_1305_; 
lean_inc(v_auxDeclToFullName_1301_);
lean_inc_ref(v_decls_1300_);
lean_inc_ref(v_fvarIdToDecl_1299_);
lean_dec_ref_known(v___x_1302_, 1);
lean_dec_ref(v_b_1271_);
v_index_1303_ = lean_ctor_get(v_localDecl_1298_, 0);
lean_inc(v_index_1303_);
v_fvarId_1304_ = lean_ctor_get(v_localDecl_1298_, 1);
lean_inc_ref(v_localDecl_1298_);
lean_inc(v_fvarId_1304_);
v___x_1305_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_fvarIdToDecl_1299_, v_fvarId_1304_, v_localDecl_1298_);
v___y_1285_ = v_localDecl_1298_;
v___y_1286_ = v_auxDeclToFullName_1301_;
v___y_1287_ = v_decls_1300_;
v___y_1288_ = v___x_1305_;
v___y_1289_ = v_index_1303_;
goto v___jp_1284_;
}
}
}
v___jp_1279_:
{
size_t v___x_1281_; size_t v___x_1282_; 
v___x_1281_ = ((size_t)1ULL);
v___x_1282_ = lean_usize_add(v_i_1270_, v___x_1281_);
v_i_1270_ = v___x_1282_;
v_b_1271_ = v_a_1280_;
goto _start;
}
v___jp_1284_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___y_1285_);
v___x_1291_ = l_Lean_PersistentArray_set___redArg(v___y_1287_, v___y_1289_, v___x_1290_);
lean_dec(v___y_1289_);
v___x_1292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1292_, 0, v___y_1288_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
lean_ctor_set(v___x_1292_, 2, v___y_1286_);
v_a_1280_ = v___x_1292_;
goto v___jp_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object* v_xs_1341_, lean_object* v_k_1342_, uint8_t v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_lctx_1350_; lean_object* v_localInstances_1351_; size_t v_sz_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v_lctx_1350_ = lean_ctor_get(v___y_1345_, 2);
v_localInstances_1351_ = lean_ctor_get(v___y_1345_, 3);
v_sz_1352_ = lean_array_size(v_xs_1341_);
v___x_1353_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1350_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_xs_1341_, v_sz_1352_, v___x_1353_, v_lctx_1350_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1356_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
lean_inc_ref(v_localInstances_1351_);
v___x_1356_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_a_1355_, v_localInstances_1351_, v_k_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v___x_1356_;
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref(v_k_1342_);
v_a_1357_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1354_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1354_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object* v_xs_1365_, lean_object* v_k_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
uint8_t v___y_27233__boxed_1374_; lean_object* v_res_1375_; 
v___y_27233__boxed_1374_ = lean_unbox(v___y_1367_);
v_res_1375_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(v_xs_1365_, v_k_1366_, v___y_27233__boxed_1374_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v_xs_1365_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object* v_e_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
uint8_t v_a_boxed_1385_; lean_object* v_res_1386_; 
v_a_boxed_1385_ = lean_unbox(v_a_1378_);
v_res_1386_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1377_, v_a_boxed_1385_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object* v___y_1387_, lean_object* v___f_1388_, lean_object* v_xs_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v___y_27183__boxed_1398_; uint8_t v___y_27185__boxed_1399_; lean_object* v_res_1400_; 
v___y_27183__boxed_1398_ = lean_unbox(v___y_1387_);
v___y_27185__boxed_1399_ = lean_unbox(v___y_1391_);
v_res_1400_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(v___y_27183__boxed_1398_, v___f_1388_, v_xs_1389_, v_b_1390_, v___y_27185__boxed_1399_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object* v_b_1401_, lean_object* v_xs_1402_, uint8_t v___y_1403_, uint8_t v___x_1404_, uint8_t v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1401_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = 1;
v___x_1415_ = l_Lean_Meta_mkForallFVars(v_xs_1402_, v_a_1413_, v___y_1403_, v___x_1404_, v___x_1404_, v___x_1414_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
return v___x_1415_;
}
else
{
return v___x_1412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object* v_b_1416_, lean_object* v_xs_1417_, lean_object* v___y_1418_, lean_object* v___x_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v___y_27219__boxed_1427_; uint8_t v___x_27220__boxed_1428_; uint8_t v___y_27221__boxed_1429_; lean_object* v_res_1430_; 
v___y_27219__boxed_1427_ = lean_unbox(v___y_1418_);
v___x_27220__boxed_1428_ = lean_unbox(v___x_1419_);
v___y_27221__boxed_1429_ = lean_unbox(v___y_1420_);
v_res_1430_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(v_b_1416_, v_xs_1417_, v___y_27219__boxed_1427_, v___x_27220__boxed_1428_, v___y_27221__boxed_1429_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v_xs_1417_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t v___y_1431_, uint8_t v___x_1432_, lean_object* v___f_1433_, lean_object* v_xs_1434_, lean_object* v_b_1435_, uint8_t v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1443_ = lean_box(v___y_1431_);
v___x_1444_ = lean_box(v___x_1432_);
lean_inc_ref(v_xs_1434_);
v___f_1445_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1445_, 0, v_b_1435_);
lean_closure_set(v___f_1445_, 1, v_xs_1434_);
lean_closure_set(v___f_1445_, 2, v___x_1443_);
lean_closure_set(v___f_1445_, 3, v___x_1444_);
v___x_1446_ = lean_box(v___y_1436_);
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
v___x_1447_ = lean_apply_9(v___f_1433_, v_xs_1434_, v___f_1445_, v___x_1446_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, lean_box(0));
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object* v___y_1448_, lean_object* v___x_1449_, lean_object* v___f_1450_, lean_object* v_xs_1451_, lean_object* v_b_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
uint8_t v___y_27194__boxed_1460_; uint8_t v___x_27195__boxed_1461_; uint8_t v___y_27197__boxed_1462_; lean_object* v_res_1463_; 
v___y_27194__boxed_1460_ = lean_unbox(v___y_1448_);
v___x_27195__boxed_1461_ = lean_unbox(v___x_1449_);
v___y_27197__boxed_1462_ = lean_unbox(v___y_1453_);
v_res_1463_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(v___y_27194__boxed_1460_, v___x_27195__boxed_1461_, v___f_1450_, v_xs_1451_, v_b_1452_, v___y_27197__boxed_1462_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t v_sz_1464_, size_t v_i_1465_, lean_object* v_bs_1466_, uint8_t v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_usize_dec_lt(v_i_1465_, v_sz_1464_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_bs_1466_);
return v___x_1475_;
}
else
{
lean_object* v_v_1476_; lean_object* v___x_1477_; lean_object* v_bs_x27_1478_; lean_object* v___x_1479_; 
v_v_1476_ = lean_array_uget(v_bs_1466_, v_i_1465_);
v___x_1477_ = lean_unsigned_to_nat(0u);
v_bs_x27_1478_ = lean_array_uset(v_bs_1466_, v_i_1465_, v___x_1477_);
v___x_1479_ = l_Lean_Meta_AbstractNestedProofs_visit(v_v_1476_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; size_t v___x_1481_; size_t v___x_1482_; lean_object* v___x_1483_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1481_ = ((size_t)1ULL);
v___x_1482_ = lean_usize_add(v_i_1465_, v___x_1481_);
v___x_1483_ = lean_array_uset(v_bs_x27_1478_, v_i_1465_, v_a_1480_);
v_i_1465_ = v___x_1482_;
v_bs_1466_ = v___x_1483_;
goto _start;
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec_ref(v_bs_x27_1478_);
v_a_1485_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1479_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1479_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_, uint8_t v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
if (lean_obj_tag(v_x_1493_) == 5)
{
lean_object* v_fn_1503_; lean_object* v_arg_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_fn_1503_ = lean_ctor_get(v_x_1493_, 0);
lean_inc_ref(v_fn_1503_);
v_arg_1504_ = lean_ctor_get(v_x_1493_, 1);
lean_inc_ref(v_arg_1504_);
lean_dec_ref_known(v_x_1493_, 2);
v___x_1505_ = lean_array_set(v_x_1494_, v_x_1495_, v_arg_1504_);
v___x_1506_ = lean_unsigned_to_nat(1u);
v___x_1507_ = lean_nat_sub(v_x_1495_, v___x_1506_);
lean_dec(v_x_1495_);
v_x_1493_ = v_fn_1503_;
v_x_1494_ = v___x_1505_;
v_x_1495_ = v___x_1507_;
goto _start;
}
else
{
lean_object* v___x_1509_; 
lean_dec(v_x_1495_);
v___x_1509_ = l_Lean_Meta_AbstractNestedProofs_visit(v_x_1493_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; size_t v_sz_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v_sz_1511_ = lean_array_size(v_x_1494_);
v___x_1512_ = ((size_t)0ULL);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_1511_, v___x_1512_, v_x_1494_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1522_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1522_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1522_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = l_Lean_mkAppN(v_a_1510_, v_a_1514_);
lean_dec(v_a_1514_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1518_);
v___x_1520_ = v___x_1516_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v_a_1510_);
v_a_1523_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1513_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1513_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
else
{
lean_dec_ref(v_x_1494_);
return v___x_1509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object* v_e_1531_, uint8_t v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_a_1540_; lean_object* v___y_1546_; lean_object* v___f_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___f_1548_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed), 9, 0);
v___x_1549_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_visit___closed__0));
v___x_1550_ = l_Lean_Core_checkSystem(v___x_1549_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1615_; 
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v___x_1550_, 0);
lean_dec(v_unused_1616_);
v___x_1552_ = v___x_1550_;
v_isShared_1553_ = v_isSharedCheck_1615_;
goto v_resetjp_1551_;
}
else
{
lean_dec(v___x_1550_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1615_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
uint8_t v___x_1554_; 
v___x_1554_ = l_Lean_Expr_isAtomic(v_e_1531_);
if (v___x_1554_ == 0)
{
uint8_t v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = 1;
v___x_1556_ = lean_st_ref_get(v_a_1533_);
v___x_1557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v___x_1556_, v_e_1531_);
lean_dec(v___x_1556_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; 
lean_del_object(v___x_1552_);
lean_inc_ref(v_e_1531_);
v___x_1558_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_1531_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; uint8_t v___y_1564_; uint8_t v___x_1598_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1598_ = lean_unbox(v_a_1559_);
lean_dec(v_a_1559_);
if (v___x_1598_ == 0)
{
v___y_1564_ = v___x_1554_;
goto v___jp_1563_;
}
else
{
uint8_t v___x_1599_; 
v___x_1599_ = l_Lean_Expr_hasSorry(v_e_1531_);
if (v___x_1599_ == 0)
{
lean_dec_ref(v___f_1548_);
goto v___jp_1560_;
}
else
{
v___y_1564_ = v___x_1554_;
goto v___jp_1563_;
}
}
v___jp_1560_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___boxed), 8, 0);
lean_inc_ref(v_e_1531_);
v___x_1562_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_e_1531_, v_a_1532_, v___x_1561_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
v___y_1546_ = v___x_1562_;
goto v___jp_1545_;
}
v___jp_1563_:
{
if (v___y_1564_ == 0)
{
switch(lean_obj_tag(v_e_1531_))
{
case 6:
{
lean_object* v___x_1565_; lean_object* v___f_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_box(v___y_1564_);
v___f_1566_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1566_, 0, v___x_1565_);
lean_closure_set(v___f_1566_, 1, v___f_1548_);
lean_inc_ref(v_e_1531_);
v___x_1567_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1531_, v___f_1566_, v___y_1564_, v___x_1555_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
v___y_1546_ = v___x_1567_;
goto v___jp_1545_;
}
case 8:
{
lean_object* v___x_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; 
v___x_1568_ = lean_box(v___y_1564_);
v___f_1569_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1569_, 0, v___x_1568_);
lean_closure_set(v___f_1569_, 1, v___f_1548_);
lean_inc_ref(v_e_1531_);
v___x_1570_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1531_, v___f_1569_, v___y_1564_, v___x_1555_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
v___y_1546_ = v___x_1570_;
goto v___jp_1545_;
}
case 7:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___f_1573_; lean_object* v___x_1574_; 
v___x_1571_ = lean_box(v___y_1564_);
v___x_1572_ = lean_box(v___x_1555_);
v___f_1573_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed), 12, 3);
lean_closure_set(v___f_1573_, 0, v___x_1571_);
lean_closure_set(v___f_1573_, 1, v___x_1572_);
lean_closure_set(v___f_1573_, 2, v___f_1548_);
lean_inc_ref(v_e_1531_);
v___x_1574_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_e_1531_, v___f_1573_, v___y_1564_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
v___y_1546_ = v___x_1574_;
goto v___jp_1545_;
}
case 10:
{
lean_object* v_data_1575_; lean_object* v_expr_1576_; lean_object* v___x_1577_; 
lean_dec_ref(v___f_1548_);
v_data_1575_ = lean_ctor_get(v_e_1531_, 0);
v_expr_1576_ = lean_ctor_get(v_e_1531_, 1);
lean_inc_ref(v_expr_1576_);
v___x_1577_ = l_Lean_Meta_AbstractNestedProofs_visit(v_expr_1576_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; size_t v___x_1579_; size_t v___x_1580_; uint8_t v___x_1581_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = lean_ptr_addr(v_expr_1576_);
v___x_1580_ = lean_ptr_addr(v_a_1578_);
v___x_1581_ = lean_usize_dec_eq(v___x_1579_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_inc(v_data_1575_);
v___x_1582_ = l_Lean_Expr_mdata___override(v_data_1575_, v_a_1578_);
v_a_1540_ = v___x_1582_;
goto v___jp_1539_;
}
else
{
lean_dec(v_a_1578_);
lean_inc_ref(v_e_1531_);
v_a_1540_ = v_e_1531_;
goto v___jp_1539_;
}
}
else
{
v___y_1546_ = v___x_1577_;
goto v___jp_1545_;
}
}
case 11:
{
lean_object* v_typeName_1583_; lean_object* v_idx_1584_; lean_object* v_struct_1585_; lean_object* v___x_1586_; 
lean_dec_ref(v___f_1548_);
v_typeName_1583_ = lean_ctor_get(v_e_1531_, 0);
v_idx_1584_ = lean_ctor_get(v_e_1531_, 1);
v_struct_1585_ = lean_ctor_get(v_e_1531_, 2);
lean_inc_ref(v_struct_1585_);
v___x_1586_ = l_Lean_Meta_AbstractNestedProofs_visit(v_struct_1585_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; size_t v___x_1588_; size_t v___x_1589_; uint8_t v___x_1590_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = lean_ptr_addr(v_struct_1585_);
v___x_1589_ = lean_ptr_addr(v_a_1587_);
v___x_1590_ = lean_usize_dec_eq(v___x_1588_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; 
lean_inc(v_idx_1584_);
lean_inc(v_typeName_1583_);
v___x_1591_ = l_Lean_Expr_proj___override(v_typeName_1583_, v_idx_1584_, v_a_1587_);
v_a_1540_ = v___x_1591_;
goto v___jp_1539_;
}
else
{
lean_dec(v_a_1587_);
lean_inc_ref(v_e_1531_);
v_a_1540_ = v_e_1531_;
goto v___jp_1539_;
}
}
else
{
v___y_1546_ = v___x_1586_;
goto v___jp_1545_;
}
}
case 5:
{
lean_object* v_dummy_1592_; lean_object* v_nargs_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec_ref(v___f_1548_);
v_dummy_1592_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_1593_ = l_Lean_Expr_getAppNumArgs(v_e_1531_);
lean_inc(v_nargs_1593_);
v___x_1594_ = lean_mk_array(v_nargs_1593_, v_dummy_1592_);
v___x_1595_ = lean_unsigned_to_nat(1u);
v___x_1596_ = lean_nat_sub(v_nargs_1593_, v___x_1595_);
lean_dec(v_nargs_1593_);
lean_inc_ref(v_e_1531_);
v___x_1597_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_e_1531_, v___x_1594_, v___x_1596_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
v___y_1546_ = v___x_1597_;
goto v___jp_1545_;
}
default: 
{
lean_dec_ref(v___f_1548_);
lean_inc_ref(v_e_1531_);
v_a_1540_ = v_e_1531_;
goto v___jp_1539_;
}
}
}
else
{
lean_dec_ref(v___f_1548_);
goto v___jp_1560_;
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v___f_1548_);
lean_dec_ref(v_e_1531_);
v_a_1600_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1558_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1558_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_object* v_val_1608_; lean_object* v___x_1610_; 
lean_dec_ref(v___f_1548_);
lean_dec_ref(v_e_1531_);
v_val_1608_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1608_);
lean_dec_ref_known(v___x_1557_, 1);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v_val_1608_);
v___x_1610_ = v___x_1552_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_val_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
else
{
lean_object* v___x_1613_; 
lean_dec_ref(v___f_1548_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v_e_1531_);
v___x_1613_ = v___x_1552_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_e_1531_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v___f_1548_);
lean_dec_ref(v_e_1531_);
v_a_1617_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1550_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1550_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
v___jp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1541_ = lean_st_ref_take(v_a_1533_);
lean_inc_ref(v_a_1540_);
v___x_1542_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v___x_1541_, v_e_1531_, v_a_1540_);
v___x_1543_ = lean_st_ref_put(v_a_1533_, v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_a_1540_);
return v___x_1544_;
}
v___jp_1545_:
{
if (lean_obj_tag(v___y_1546_) == 0)
{
lean_object* v_a_1547_; 
v_a_1547_ = lean_ctor_get(v___y_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___y_1546_, 1);
v_a_1540_ = v_a_1547_;
goto v___jp_1539_;
}
else
{
lean_dec_ref(v_e_1531_);
return v___y_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object* v_b_1625_, lean_object* v_xs_1626_, uint8_t v___y_1627_, uint8_t v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1625_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = 1;
v___x_1638_ = l_Lean_Meta_mkLambdaFVars(v_xs_1626_, v_a_1636_, v___y_1627_, v___y_1627_, v___y_1627_, v___y_1627_, v___x_1637_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1638_;
}
else
{
return v___x_1635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object* v_b_1639_, lean_object* v_xs_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v___y_27206__boxed_1649_; uint8_t v___y_27207__boxed_1650_; lean_object* v_res_1651_; 
v___y_27206__boxed_1649_ = lean_unbox(v___y_1641_);
v___y_27207__boxed_1650_ = lean_unbox(v___y_1642_);
v_res_1651_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(v_b_1639_, v_xs_1640_, v___y_27206__boxed_1649_, v___y_27207__boxed_1650_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v_xs_1640_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t v___y_1652_, lean_object* v___f_1653_, lean_object* v_xs_1654_, lean_object* v_b_1655_, uint8_t v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1663_ = lean_box(v___y_1652_);
lean_inc_ref(v_xs_1654_);
v___f_1664_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1664_, 0, v_b_1655_);
lean_closure_set(v___f_1664_, 1, v_xs_1654_);
lean_closure_set(v___f_1664_, 2, v___x_1663_);
v___x_1665_ = lean_box(v___y_1656_);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v___y_1657_);
v___x_1666_ = lean_apply_9(v___f_1653_, v_xs_1654_, v___f_1664_, v___x_1665_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, lean_box(0));
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object* v_sz_1667_, lean_object* v_i_1668_, lean_object* v_bs_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
size_t v_sz_boxed_1677_; size_t v_i_boxed_1678_; uint8_t v___y_27246__boxed_1679_; lean_object* v_res_1680_; 
v_sz_boxed_1677_ = lean_unbox_usize(v_sz_1667_);
lean_dec(v_sz_1667_);
v_i_boxed_1678_ = lean_unbox_usize(v_i_1668_);
lean_dec(v_i_1668_);
v___y_27246__boxed_1679_ = lean_unbox(v___y_1670_);
v_res_1680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_boxed_1677_, v_i_boxed_1678_, v_bs_1669_, v___y_27246__boxed_1679_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object* v_x_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v___y_27267__boxed_1691_; lean_object* v_res_1692_; 
v___y_27267__boxed_1691_ = lean_unbox(v___y_1684_);
v_res_1692_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_x_1681_, v_x_1682_, v_x_1683_, v___y_27267__boxed_1691_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object* v_as_1693_, lean_object* v_sz_1694_, lean_object* v_i_1695_, lean_object* v_b_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
size_t v_sz_boxed_1704_; size_t v_i_boxed_1705_; uint8_t v___y_27290__boxed_1706_; lean_object* v_res_1707_; 
v_sz_boxed_1704_ = lean_unbox_usize(v_sz_1694_);
lean_dec(v_sz_1694_);
v_i_boxed_1705_ = lean_unbox_usize(v_i_1695_);
lean_dec(v_i_1695_);
v___y_27290__boxed_1706_ = lean_unbox(v___y_1697_);
v_res_1707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_as_1693_, v_sz_boxed_1704_, v_i_boxed_1705_, v_b_1696_, v___y_27290__boxed_1706_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v_as_1693_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object* v_00_u03b2_1708_, lean_object* v_x_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_x_1709_, v_x_1710_, v_x_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object* v_00_u03b2_1713_, lean_object* v_m_1714_, lean_object* v_a_1715_, lean_object* v_b_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_m_1714_, v_a_1715_, v_b_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object* v_00_u03b2_1718_, lean_object* v_m_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_m_1719_, v_a_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object* v_00_u03b2_1722_, lean_object* v_m_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_00_u03b2_1722_, v_m_1723_, v_a_1724_);
lean_dec_ref(v_a_1724_);
lean_dec_ref(v_m_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object* v_00_u03b2_1726_, lean_object* v_x_1727_, size_t v_x_1728_, size_t v_x_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_1727_, v_x_1728_, v_x_1729_, v_x_1730_, v_x_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_, lean_object* v_x_1736_, lean_object* v_x_1737_, lean_object* v_x_1738_){
_start:
{
size_t v_x_27870__boxed_1739_; size_t v_x_27871__boxed_1740_; lean_object* v_res_1741_; 
v_x_27870__boxed_1739_ = lean_unbox_usize(v_x_1735_);
lean_dec(v_x_1735_);
v_x_27871__boxed_1740_ = lean_unbox_usize(v_x_1736_);
lean_dec(v_x_1736_);
v_res_1741_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(v_00_u03b2_1733_, v_x_1734_, v_x_27870__boxed_1739_, v_x_27871__boxed_1740_, v_x_1737_, v_x_1738_);
return v_res_1741_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(lean_object* v_00_u03b2_1742_, lean_object* v_a_1743_, lean_object* v_x_1744_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_1743_, v_x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1746_, lean_object* v_a_1747_, lean_object* v_x_1748_){
_start:
{
uint8_t v_res_1749_; lean_object* v_r_1750_; 
v_res_1749_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(v_00_u03b2_1746_, v_a_1747_, v_x_1748_);
lean_dec(v_x_1748_);
lean_dec_ref(v_a_1747_);
v_r_1750_ = lean_box(v_res_1749_);
return v_r_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6(lean_object* v_00_u03b2_1751_, lean_object* v_data_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(v_data_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7(lean_object* v_00_u03b2_1754_, lean_object* v_a_1755_, lean_object* v_b_1756_, lean_object* v_x_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_1755_, v_b_1756_, v_x_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(lean_object* v_00_u03b2_1759_, lean_object* v_a_1760_, lean_object* v_x_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1760_, v_x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1763_, lean_object* v_a_1764_, lean_object* v_x_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(v_00_u03b2_1763_, v_a_1764_, v_x_1765_);
lean_dec(v_x_1765_);
lean_dec_ref(v_a_1764_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17(lean_object* v_00_u03b1_1767_, lean_object* v_x_1768_, uint8_t v_isExporting_1769_, uint8_t v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(v_x_1768_, v_isExporting_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___boxed(lean_object* v_00_u03b1_1778_, lean_object* v_x_1779_, lean_object* v_isExporting_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
uint8_t v_isExporting_boxed_1788_; uint8_t v___y_27902__boxed_1789_; lean_object* v_res_1790_; 
v_isExporting_boxed_1788_ = lean_unbox(v_isExporting_1780_);
v___y_27902__boxed_1789_ = lean_unbox(v___y_1781_);
v_res_1790_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17(v_00_u03b1_1778_, v_x_1779_, v_isExporting_boxed_1788_, v___y_27902__boxed_1789_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11(lean_object* v_00_u03b1_1791_, lean_object* v_x_1792_, uint8_t v_when_1793_, uint8_t v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(v_x_1792_, v_when_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___boxed(lean_object* v_00_u03b1_1802_, lean_object* v_x_1803_, lean_object* v_when_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
uint8_t v_when_boxed_1812_; uint8_t v___y_27925__boxed_1813_; lean_object* v_res_1814_; 
v_when_boxed_1812_ = lean_unbox(v_when_1804_);
v___y_27925__boxed_1813_ = lean_unbox(v___y_1805_);
v_res_1814_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11(v_00_u03b1_1802_, v_x_1803_, v_when_boxed_1812_, v___y_27925__boxed_1813_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_1815_, lean_object* v_n_1816_, lean_object* v_k_1817_, lean_object* v_v_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(v_n_1816_, v_k_1817_, v_v_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_1820_, size_t v_depth_1821_, lean_object* v_keys_1822_, lean_object* v_vals_1823_, lean_object* v_heq_1824_, lean_object* v_i_1825_, lean_object* v_entries_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_depth_1821_, v_keys_1822_, v_vals_1823_, v_i_1825_, v_entries_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_1828_, lean_object* v_depth_1829_, lean_object* v_keys_1830_, lean_object* v_vals_1831_, lean_object* v_heq_1832_, lean_object* v_i_1833_, lean_object* v_entries_1834_){
_start:
{
size_t v_depth_boxed_1835_; lean_object* v_res_1836_; 
v_depth_boxed_1835_ = lean_unbox_usize(v_depth_1829_);
lean_dec(v_depth_1829_);
v_res_1836_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(v_00_u03b2_1828_, v_depth_boxed_1835_, v_keys_1830_, v_vals_1831_, v_heq_1832_, v_i_1833_, v_entries_1834_);
lean_dec_ref(v_vals_1831_);
lean_dec_ref(v_keys_1830_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_1837_, lean_object* v_i_1838_, lean_object* v_source_1839_, lean_object* v_target_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(v_i_1838_, v_source_1839_, v_target_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_, lean_object* v_x_1845_, lean_object* v_x_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(v_x_1843_, v_x_1844_, v_x_1845_, v_x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16(lean_object* v_00_u03b2_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(v_x_1849_, v_x_1850_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__0(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_box(0);
v___x_1853_ = lean_unsigned_to_nat(16u);
v___x_1854_ = lean_mk_array(v___x_1853_, v___x_1852_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__1(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__0, &l_Lean_Meta_abstractNestedProofs___closed__0_once, _init_l_Lean_Meta_abstractNestedProofs___closed__0);
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
lean_ctor_set(v___x_1857_, 1, v___x_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs(lean_object* v_e_1858_, uint8_t v_cache_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1865_; 
lean_inc_ref(v_e_1858_);
v___x_1865_ = l_Lean_Meta_isProof(v_e_1858_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1886_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1886_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1886_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
uint8_t v___x_1870_; 
v___x_1870_ = lean_unbox(v_a_1866_);
lean_dec(v_a_1866_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
lean_del_object(v___x_1868_);
v___x_1871_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__1, &l_Lean_Meta_abstractNestedProofs___closed__1_once, _init_l_Lean_Meta_abstractNestedProofs___closed__1);
v___x_1872_ = lean_st_mk_ref(v___x_1871_);
v___x_1873_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1858_, v_cache_1859_, v___x_1872_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1882_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_st_ref_get(v___x_1872_);
lean_dec(v___x_1872_);
lean_dec(v___x_1878_);
if (v_isShared_1877_ == 0)
{
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1874_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
lean_dec(v___x_1872_);
return v___x_1873_;
}
}
else
{
lean_object* v___x_1884_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v_e_1858_);
v___x_1884_ = v___x_1868_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_e_1858_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec_ref(v_e_1858_);
v_a_1887_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1865_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1865_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object* v_e_1895_, lean_object* v_cache_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
uint8_t v_cache_boxed_1902_; lean_object* v_res_1903_; 
v_cache_boxed_1902_ = lean_unbox(v_cache_1896_);
v_res_1903_ = l_Lean_Meta_abstractNestedProofs(v_e_1895_, v_cache_boxed_1902_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
return v_res_1903_;
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
