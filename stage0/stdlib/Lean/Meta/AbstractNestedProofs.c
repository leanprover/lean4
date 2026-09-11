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
uint8_t v_a_4070__boxed_143_; uint8_t v___x_4071__boxed_144_; size_t v_i_boxed_145_; size_t v_stop_boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v_a_4070__boxed_143_ = lean_unbox(v_a_138_);
v___x_4071__boxed_144_ = lean_unbox(v___x_139_);
v_i_boxed_145_ = lean_unbox_usize(v_i_141_);
lean_dec(v_i_141_);
v_stop_boxed_146_ = lean_unbox_usize(v_stop_142_);
lean_dec(v_stop_142_);
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_4070__boxed_143_, v___x_4071__boxed_144_, v_as_140_, v_i_boxed_145_, v_stop_boxed_146_);
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
uint8_t v_a_4096__boxed_191_; uint8_t v___x_4097__boxed_192_; lean_object* v_res_193_; 
v_a_4096__boxed_191_ = lean_unbox(v_a_184_);
v___x_4097__boxed_192_ = lean_unbox(v___x_185_);
v_res_193_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(v_a_4096__boxed_191_, v___x_4097__boxed_192_, v___x_186_, v_x_187_, v_x_188_, v_x_189_);
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
uint8_t v_a_4174__boxed_244_; uint8_t v___x_4175__boxed_245_; lean_object* v_res_246_; 
v_a_4174__boxed_244_ = lean_unbox(v_a_233_);
v___x_4175__boxed_245_ = lean_unbox(v___x_234_);
v_res_246_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(v_a_4174__boxed_244_, v___x_4175__boxed_245_, v___x_235_, v_x_236_, v_x_237_, v_x_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
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
lean_object* v___x_301_; lean_object* v_env_302_; lean_object* v_nextMacroScope_303_; lean_object* v_ngen_304_; lean_object* v_auxDeclNGen_305_; lean_object* v_traceState_306_; lean_object* v_messages_307_; lean_object* v_infoState_308_; lean_object* v_snapshotTasks_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_334_; 
v___x_301_ = lean_st_ref_take(v___y_294_);
v_env_302_ = lean_ctor_get(v___x_301_, 0);
v_nextMacroScope_303_ = lean_ctor_get(v___x_301_, 1);
v_ngen_304_ = lean_ctor_get(v___x_301_, 2);
v_auxDeclNGen_305_ = lean_ctor_get(v___x_301_, 3);
v_traceState_306_ = lean_ctor_get(v___x_301_, 4);
v_messages_307_ = lean_ctor_get(v___x_301_, 6);
v_infoState_308_ = lean_ctor_get(v___x_301_, 7);
v_snapshotTasks_309_ = lean_ctor_get(v___x_301_, 8);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v___x_301_, 5);
lean_dec(v_unused_335_);
v___x_311_ = v___x_301_;
v_isShared_312_ = v_isSharedCheck_334_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_snapshotTasks_309_);
lean_inc(v_infoState_308_);
lean_inc(v_messages_307_);
lean_inc(v_traceState_306_);
lean_inc(v_auxDeclNGen_305_);
lean_inc(v_ngen_304_);
lean_inc(v_nextMacroScope_303_);
lean_inc(v_env_302_);
lean_dec(v___x_301_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_334_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = l_Lean_Environment_setExporting(v_env_302_, v_isExporting_295_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 5, v___x_296_);
lean_ctor_set(v___x_311_, 0, v___x_313_);
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_nextMacroScope_303_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_ngen_304_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_auxDeclNGen_305_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v_traceState_306_);
lean_ctor_set(v_reuseFailAlloc_333_, 5, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_333_, 6, v_messages_307_);
lean_ctor_set(v_reuseFailAlloc_333_, 7, v_infoState_308_);
lean_ctor_set(v_reuseFailAlloc_333_, 8, v_snapshotTasks_309_);
v___x_315_ = v_reuseFailAlloc_333_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_mctx_318_; lean_object* v_zetaDeltaFVarIds_319_; lean_object* v_postponed_320_; lean_object* v_diag_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_331_; 
v___x_316_ = lean_st_ref_put(v___y_294_, v___x_315_);
v___x_317_ = lean_st_ref_take(v___y_297_);
v_mctx_318_ = lean_ctor_get(v___x_317_, 0);
v_zetaDeltaFVarIds_319_ = lean_ctor_get(v___x_317_, 2);
v_postponed_320_ = lean_ctor_get(v___x_317_, 3);
v_diag_321_ = lean_ctor_get(v___x_317_, 4);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v___x_317_, 1);
lean_dec(v_unused_332_);
v___x_323_ = v___x_317_;
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_diag_321_);
lean_inc(v_postponed_320_);
lean_inc(v_zetaDeltaFVarIds_319_);
lean_inc(v_mctx_318_);
lean_dec(v___x_317_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_box(0);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_298_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_mctx_318_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_zetaDeltaFVarIds_319_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_postponed_320_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v_diag_321_);
v___x_327_ = v_reuseFailAlloc_330_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_st_ref_put(v___y_297_, v___x_327_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_325_);
return v___x_329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v___y_336_, lean_object* v_isExporting_337_, lean_object* v___x_338_, lean_object* v___y_339_, lean_object* v___x_340_, lean_object* v_a_x3f_341_, lean_object* v___y_342_){
_start:
{
uint8_t v_isExporting_boxed_343_; lean_object* v_res_344_; 
v_isExporting_boxed_343_ = lean_unbox(v_isExporting_337_);
v_res_344_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_336_, v_isExporting_boxed_343_, v___x_338_, v___y_339_, v___x_340_, v_a_x3f_341_);
lean_dec(v_a_x3f_341_);
lean_dec(v___y_339_);
lean_dec(v___y_336_);
return v_res_344_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_345_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1);
v___x_351_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
lean_ctor_set(v___x_351_, 2, v___x_350_);
lean_ctor_set(v___x_351_, 3, v___x_350_);
lean_ctor_set(v___x_351_, 4, v___x_350_);
lean_ctor_set(v___x_351_, 5, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(lean_object* v_x_352_, uint8_t v_isExporting_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; lean_object* v_env_360_; lean_object* v___x_361_; uint8_t v_isModule_362_; 
v___x_359_ = lean_st_ref_get(v___y_357_);
v_env_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc_ref(v_env_360_);
lean_dec(v___x_359_);
v___x_361_ = l_Lean_Environment_header(v_env_360_);
v_isModule_362_ = lean_ctor_get_uint8(v___x_361_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_361_);
if (v_isModule_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec_ref(v_env_360_);
lean_inc(v___y_357_);
lean_inc_ref(v___y_356_);
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
v___x_363_ = lean_apply_5(v_x_352_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, lean_box(0));
return v___x_363_;
}
else
{
uint8_t v_isExporting_364_; 
v_isExporting_364_ = lean_ctor_get_uint8(v_env_360_, sizeof(void*)*8);
lean_dec_ref(v_env_360_);
if (v_isExporting_353_ == 0)
{
if (v_isExporting_364_ == 0)
{
lean_object* v___x_430_; 
lean_inc(v___y_357_);
lean_inc_ref(v___y_356_);
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
v___x_430_ = lean_apply_5(v_x_352_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, lean_box(0));
return v___x_430_;
}
else
{
goto v___jp_365_;
}
}
else
{
if (v_isExporting_364_ == 0)
{
goto v___jp_365_;
}
else
{
lean_object* v___x_431_; 
lean_inc(v___y_357_);
lean_inc_ref(v___y_356_);
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
v___x_431_ = lean_apply_5(v_x_352_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, lean_box(0));
return v___x_431_;
}
}
v___jp_365_:
{
lean_object* v___x_366_; lean_object* v_env_367_; lean_object* v_nextMacroScope_368_; lean_object* v_ngen_369_; lean_object* v_auxDeclNGen_370_; lean_object* v_traceState_371_; lean_object* v_messages_372_; lean_object* v_infoState_373_; lean_object* v_snapshotTasks_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_428_; 
v___x_366_ = lean_st_ref_take(v___y_357_);
v_env_367_ = lean_ctor_get(v___x_366_, 0);
v_nextMacroScope_368_ = lean_ctor_get(v___x_366_, 1);
v_ngen_369_ = lean_ctor_get(v___x_366_, 2);
v_auxDeclNGen_370_ = lean_ctor_get(v___x_366_, 3);
v_traceState_371_ = lean_ctor_get(v___x_366_, 4);
v_messages_372_ = lean_ctor_get(v___x_366_, 6);
v_infoState_373_ = lean_ctor_get(v___x_366_, 7);
v_snapshotTasks_374_ = lean_ctor_get(v___x_366_, 8);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; 
v_unused_429_ = lean_ctor_get(v___x_366_, 5);
lean_dec(v_unused_429_);
v___x_376_ = v___x_366_;
v_isShared_377_ = v_isSharedCheck_428_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_snapshotTasks_374_);
lean_inc(v_infoState_373_);
lean_inc(v_messages_372_);
lean_inc(v_traceState_371_);
lean_inc(v_auxDeclNGen_370_);
lean_inc(v_ngen_369_);
lean_inc(v_nextMacroScope_368_);
lean_inc(v_env_367_);
lean_dec(v___x_366_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_428_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_378_ = l_Lean_Environment_setExporting(v_env_367_, v_isExporting_353_);
v___x_379_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 5, v___x_379_);
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_381_ = v___x_376_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_nextMacroScope_368_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_ngen_369_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_auxDeclNGen_370_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v_traceState_371_);
lean_ctor_set(v_reuseFailAlloc_427_, 5, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_427_, 6, v_messages_372_);
lean_ctor_set(v_reuseFailAlloc_427_, 7, v_infoState_373_);
lean_ctor_set(v_reuseFailAlloc_427_, 8, v_snapshotTasks_374_);
v___x_381_ = v_reuseFailAlloc_427_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_mctx_384_; lean_object* v_zetaDeltaFVarIds_385_; lean_object* v_postponed_386_; lean_object* v_diag_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_425_; 
v___x_382_ = lean_st_ref_put(v___y_357_, v___x_381_);
v___x_383_ = lean_st_ref_take(v___y_355_);
v_mctx_384_ = lean_ctor_get(v___x_383_, 0);
v_zetaDeltaFVarIds_385_ = lean_ctor_get(v___x_383_, 2);
v_postponed_386_ = lean_ctor_get(v___x_383_, 3);
v_diag_387_ = lean_ctor_get(v___x_383_, 4);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v___x_383_, 1);
lean_dec(v_unused_426_);
v___x_389_ = v___x_383_;
v_isShared_390_ = v_isSharedCheck_425_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_diag_387_);
lean_inc(v_postponed_386_);
lean_inc(v_zetaDeltaFVarIds_385_);
lean_inc(v_mctx_384_);
lean_dec(v___x_383_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_425_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v___x_391_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_mctx_384_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_zetaDeltaFVarIds_385_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_postponed_386_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_diag_387_);
v___x_393_ = v_reuseFailAlloc_424_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v_r_395_; 
v___x_394_ = lean_st_ref_put(v___y_355_, v___x_393_);
lean_inc(v___y_357_);
lean_inc_ref(v___y_356_);
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
v_r_395_ = lean_apply_5(v_x_352_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, lean_box(0));
if (lean_obj_tag(v_r_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_412_; 
v_a_396_ = lean_ctor_get(v_r_395_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v_r_395_);
if (v_isSharedCheck_412_ == 0)
{
v___x_398_ = v_r_395_;
v_isShared_399_ = v_isSharedCheck_412_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v_r_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_412_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
lean_inc(v_a_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 1);
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_411_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v___x_402_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_357_, v_isExporting_364_, v___x_379_, v___y_355_, v___x_391_, v___x_401_);
lean_dec_ref(v___x_401_);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_402_, 0);
lean_dec(v_unused_410_);
v___x_404_ = v___x_402_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_dec(v___x_402_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v_a_396_);
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_396_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v_a_413_ = lean_ctor_get(v_r_395_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v_r_395_, 1);
v___x_414_ = lean_box(0);
v___x_415_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_357_, v_isExporting_364_, v___x_379_, v___y_355_, v___x_391_, v___x_414_);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v___x_415_, 0);
lean_dec(v_unused_423_);
v___x_417_ = v___x_415_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_dec(v___x_415_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 1);
lean_ctor_set(v___x_417_, 0, v_a_413_);
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_413_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___boxed(lean_object* v_x_432_, lean_object* v_isExporting_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
uint8_t v_isExporting_boxed_439_; lean_object* v_res_440_; 
v_isExporting_boxed_439_ = lean_unbox(v_isExporting_433_);
v_res_440_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(v_x_432_, v_isExporting_boxed_439_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object* v_x_441_, uint8_t v_when_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
if (v_when_442_ == 0)
{
lean_object* v___x_448_; 
lean_inc(v___y_446_);
lean_inc_ref(v___y_445_);
lean_inc(v___y_444_);
lean_inc_ref(v___y_443_);
v___x_448_ = lean_apply_5(v_x_441_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, lean_box(0));
return v___x_448_;
}
else
{
uint8_t v___x_449_; lean_object* v___x_450_; 
v___x_449_ = 0;
v___x_450_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(v_x_441_, v___x_449_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object* v_x_451_, lean_object* v_when_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
uint8_t v_when_boxed_458_; lean_object* v_res_459_; 
v_when_boxed_458_ = lean_unbox(v_when_452_);
v_res_459_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_451_, v_when_boxed_458_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object* v_e_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_466_; lean_object* v_env_467_; lean_object* v___f_468_; uint8_t v___x_469_; lean_object* v___x_470_; 
v___x_466_ = lean_st_ref_get(v_a_464_);
v_env_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc_ref(v_env_467_);
lean_dec(v___x_466_);
v___f_468_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed), 7, 2);
lean_closure_set(v___f_468_, 0, v_e_460_);
lean_closure_set(v___f_468_, 1, v_env_467_);
v___x_469_ = 1;
v___x_470_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v___f_468_, v___x_469_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object* v_e_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3(lean_object* v_00_u03b1_478_, lean_object* v_x_479_, uint8_t v_isExporting_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(v_x_479_, v_isExporting_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___boxed(lean_object* v_00_u03b1_487_, lean_object* v_x_488_, lean_object* v_isExporting_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
uint8_t v_isExporting_boxed_495_; lean_object* v_res_496_; 
v_isExporting_boxed_495_ = lean_unbox(v_isExporting_489_);
v_res_496_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3(v_00_u03b1_487_, v_x_488_, v_isExporting_boxed_495_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object* v_00_u03b1_497_, lean_object* v_x_498_, uint8_t v_when_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_498_, v_when_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object* v_00_u03b1_506_, lean_object* v_x_507_, lean_object* v_when_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
uint8_t v_when_boxed_514_; lean_object* v_res_515_; 
v_when_boxed_514_ = lean_unbox(v_when_508_);
v_res_515_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(v_00_u03b1_506_, v_x_507_, v_when_boxed_514_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1(uint8_t v_a_516_, uint8_t v___x_517_, lean_object* v___x_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(v_a_516_, v___x_517_, v___x_518_, v_x_519_, v_x_520_, v_x_521_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___boxed(lean_object* v_a_528_, lean_object* v___x_529_, lean_object* v___x_530_, lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
uint8_t v_a_4639__boxed_539_; uint8_t v___x_4640__boxed_540_; lean_object* v_res_541_; 
v_a_4639__boxed_539_ = lean_unbox(v_a_528_);
v___x_4640__boxed_540_ = lean_unbox(v___x_529_);
v_res_541_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1(v_a_4639__boxed_539_, v___x_4640__boxed_540_, v___x_530_, v_x_531_, v_x_532_, v_x_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(lean_object* v_x_542_, uint8_t v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_box(v___y_543_);
lean_inc(v___y_544_);
v___x_551_ = lean_apply_7(v_x_542_, v___x_550_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, lean_box(0));
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed(lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
uint8_t v___y_26081__boxed_560_; lean_object* v_res_561_; 
v___y_26081__boxed_560_ = lean_unbox(v___y_553_);
v_res_561_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(v_x_552_, v___y_26081__boxed_560_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_554_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object* v_lctx_562_, lean_object* v_localInsts_563_, lean_object* v_x_564_, uint8_t v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v___f_573_; lean_object* v___x_574_; 
v___x_572_ = lean_box(v___y_565_);
lean_inc(v___y_566_);
v___f_573_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_573_, 0, v_x_564_);
lean_closure_set(v___f_573_, 1, v___x_572_);
lean_closure_set(v___f_573_, 2, v___y_566_);
v___x_574_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_562_, v_localInsts_563_, v___f_573_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
if (lean_obj_tag(v___x_574_) == 0)
{
return v___x_574_;
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___boxed(lean_object* v_lctx_583_, lean_object* v_localInsts_584_, lean_object* v_x_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
uint8_t v___y_26106__boxed_593_; lean_object* v_res_594_; 
v___y_26106__boxed_593_ = lean_unbox(v___y_586_);
v_res_594_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_lctx_583_, v_localInsts_584_, v_x_585_, v___y_26106__boxed_593_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object* v_00_u03b1_595_, lean_object* v_lctx_596_, lean_object* v_localInsts_597_, lean_object* v_x_598_, uint8_t v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_lctx_596_, v_localInsts_597_, v_x_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object* v_00_u03b1_607_, lean_object* v_lctx_608_, lean_object* v_localInsts_609_, lean_object* v_x_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
uint8_t v___y_26150__boxed_618_; lean_object* v_res_619_; 
v___y_26150__boxed_618_ = lean_unbox(v___y_611_);
v_res_619_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_00_u03b1_607_, v_lctx_608_, v_localInsts_609_, v_x_610_, v___y_26150__boxed_618_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(lean_object* v_k_620_, uint8_t v___y_621_, lean_object* v___y_622_, lean_object* v_b_623_, lean_object* v_c_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_box(v___y_621_);
lean_inc(v___y_628_);
lean_inc_ref(v___y_627_);
lean_inc(v___y_626_);
lean_inc_ref(v___y_625_);
lean_inc(v___y_622_);
v___x_631_ = lean_apply_9(v_k_620_, v_b_623_, v_c_624_, v___x_630_, v___y_622_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, lean_box(0));
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed(lean_object* v_k_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v_b_635_, lean_object* v_c_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
uint8_t v___y_26173__boxed_642_; lean_object* v_res_643_; 
v___y_26173__boxed_642_ = lean_unbox(v___y_633_);
v_res_643_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(v_k_632_, v___y_26173__boxed_642_, v___y_634_, v_b_635_, v_c_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_634_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object* v_e_644_, lean_object* v_k_645_, uint8_t v_cleanupAnnotations_646_, uint8_t v_preserveNondepLet_647_, uint8_t v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; lean_object* v___f_656_; uint8_t v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_655_ = lean_box(v___y_648_);
lean_inc(v___y_649_);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_656_, 0, v_k_645_);
lean_closure_set(v___f_656_, 1, v___x_655_);
lean_closure_set(v___f_656_, 2, v___y_649_);
v___x_657_ = 1;
v___x_658_ = 0;
v___x_659_ = lean_box(0);
v___x_660_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_644_, v___x_657_, v___x_657_, v_preserveNondepLet_647_, v___x_658_, v___x_659_, v___f_656_, v_cleanupAnnotations_646_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
if (lean_obj_tag(v___x_660_) == 0)
{
return v___x_660_;
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object* v_e_669_, lean_object* v_k_670_, lean_object* v_cleanupAnnotations_671_, lean_object* v_preserveNondepLet_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_680_; uint8_t v_preserveNondepLet_boxed_681_; uint8_t v___y_26198__boxed_682_; lean_object* v_res_683_; 
v_cleanupAnnotations_boxed_680_ = lean_unbox(v_cleanupAnnotations_671_);
v_preserveNondepLet_boxed_681_ = lean_unbox(v_preserveNondepLet_672_);
v___y_26198__boxed_682_ = lean_unbox(v___y_673_);
v_res_683_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_669_, v_k_670_, v_cleanupAnnotations_boxed_680_, v_preserveNondepLet_boxed_681_, v___y_26198__boxed_682_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object* v_00_u03b1_684_, lean_object* v_e_685_, lean_object* v_k_686_, uint8_t v_cleanupAnnotations_687_, uint8_t v_preserveNondepLet_688_, uint8_t v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_685_, v_k_686_, v_cleanupAnnotations_687_, v_preserveNondepLet_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object* v_00_u03b1_697_, lean_object* v_e_698_, lean_object* v_k_699_, lean_object* v_cleanupAnnotations_700_, lean_object* v_preserveNondepLet_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_709_; uint8_t v_preserveNondepLet_boxed_710_; uint8_t v___y_26248__boxed_711_; lean_object* v_res_712_; 
v_cleanupAnnotations_boxed_709_ = lean_unbox(v_cleanupAnnotations_700_);
v_preserveNondepLet_boxed_710_ = lean_unbox(v_preserveNondepLet_701_);
v___y_26248__boxed_711_ = lean_unbox(v___y_702_);
v_res_712_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(v_00_u03b1_697_, v_e_698_, v_k_699_, v_cleanupAnnotations_boxed_709_, v_preserveNondepLet_boxed_710_, v___y_26248__boxed_711_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(lean_object* v_type_713_, lean_object* v_k_714_, uint8_t v_cleanupAnnotations_715_, uint8_t v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; lean_object* v___f_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_723_ = lean_box(v___y_716_);
lean_inc(v___y_717_);
v___f_724_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_724_, 0, v_k_714_);
lean_closure_set(v___f_724_, 1, v___x_723_);
lean_closure_set(v___f_724_, 2, v___y_717_);
v___x_725_ = 0;
v___x_726_ = lean_box(0);
v___x_727_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_725_, v___x_726_, v_type_713_, v___f_724_, v_cleanupAnnotations_715_, v___x_725_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_727_) == 0)
{
return v___x_727_;
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___boxed(lean_object* v_type_736_, lean_object* v_k_737_, lean_object* v_cleanupAnnotations_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_746_; uint8_t v___y_26271__boxed_747_; lean_object* v_res_748_; 
v_cleanupAnnotations_boxed_746_ = lean_unbox(v_cleanupAnnotations_738_);
v___y_26271__boxed_747_ = lean_unbox(v___y_739_);
v_res_748_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_736_, v_k_737_, v_cleanupAnnotations_boxed_746_, v___y_26271__boxed_747_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object* v_00_u03b1_749_, lean_object* v_type_750_, lean_object* v_k_751_, uint8_t v_cleanupAnnotations_752_, uint8_t v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_750_, v_k_751_, v_cleanupAnnotations_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object* v_00_u03b1_761_, lean_object* v_type_762_, lean_object* v_k_763_, lean_object* v_cleanupAnnotations_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_772_; uint8_t v___y_26319__boxed_773_; lean_object* v_res_774_; 
v_cleanupAnnotations_boxed_772_ = lean_unbox(v_cleanupAnnotations_764_);
v___y_26319__boxed_773_ = lean_unbox(v___y_765_);
v_res_774_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_00_u03b1_761_, v_type_762_, v_k_763_, v_cleanupAnnotations_boxed_772_, v___y_26319__boxed_773_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_x_775_, lean_object* v_x_776_, lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
lean_object* v_ks_779_; lean_object* v_vs_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_804_; 
v_ks_779_ = lean_ctor_get(v_x_775_, 0);
v_vs_780_ = lean_ctor_get(v_x_775_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_775_);
if (v_isSharedCheck_804_ == 0)
{
v___x_782_ = v_x_775_;
v_isShared_783_ = v_isSharedCheck_804_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_vs_780_);
lean_inc(v_ks_779_);
lean_dec(v_x_775_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_804_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = lean_array_get_size(v_ks_779_);
v___x_785_ = lean_nat_dec_lt(v_x_776_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
lean_dec(v_x_776_);
v___x_786_ = lean_array_push(v_ks_779_, v_x_777_);
v___x_787_ = lean_array_push(v_vs_780_, v_x_778_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___x_787_);
lean_ctor_set(v___x_782_, 0, v___x_786_);
v___x_789_ = v___x_782_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
else
{
lean_object* v_k_x27_791_; uint8_t v___x_792_; 
v_k_x27_791_ = lean_array_fget_borrowed(v_ks_779_, v_x_776_);
v___x_792_ = l_Lean_instBEqFVarId_beq(v_x_777_, v_k_x27_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_794_; 
if (v_isShared_783_ == 0)
{
v___x_794_ = v___x_782_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_ks_779_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_vs_780_);
v___x_794_ = v_reuseFailAlloc_798_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_unsigned_to_nat(1u);
v___x_796_ = lean_nat_add(v_x_776_, v___x_795_);
lean_dec(v_x_776_);
v_x_775_ = v___x_794_;
v_x_776_ = v___x_796_;
goto _start;
}
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_799_ = lean_array_fset(v_ks_779_, v_x_776_, v_x_777_);
v___x_800_ = lean_array_fset(v_vs_780_, v_x_776_, v_x_778_);
lean_dec(v_x_776_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___x_800_);
lean_ctor_set(v___x_782_, 0, v___x_799_);
v___x_802_ = v___x_782_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(lean_object* v_n_805_, lean_object* v_k_806_, lean_object* v_v_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(v_n_805_, v___x_808_, v_k_806_, v_v_807_);
return v___x_809_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object* v_x_811_, size_t v_x_812_, size_t v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
if (lean_obj_tag(v_x_811_) == 0)
{
lean_object* v_es_816_; size_t v___x_817_; size_t v___x_818_; lean_object* v_j_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v_es_816_ = lean_ctor_get(v_x_811_, 0);
v___x_817_ = ((size_t)31ULL);
v___x_818_ = lean_usize_land(v_x_812_, v___x_817_);
v_j_819_ = lean_usize_to_nat(v___x_818_);
v___x_820_ = lean_array_get_size(v_es_816_);
v___x_821_ = lean_nat_dec_lt(v_j_819_, v___x_820_);
if (v___x_821_ == 0)
{
lean_dec(v_j_819_);
lean_dec(v_x_815_);
lean_dec(v_x_814_);
return v_x_811_;
}
else
{
lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_860_; 
lean_inc_ref(v_es_816_);
v_isSharedCheck_860_ = !lean_is_exclusive(v_x_811_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_x_811_, 0);
lean_dec(v_unused_861_);
v___x_823_ = v_x_811_;
v_isShared_824_ = v_isSharedCheck_860_;
goto v_resetjp_822_;
}
else
{
lean_dec(v_x_811_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_860_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_v_825_; lean_object* v___x_826_; lean_object* v_xs_x27_827_; lean_object* v___y_829_; 
v_v_825_ = lean_array_fget(v_es_816_, v_j_819_);
v___x_826_ = lean_box(0);
v_xs_x27_827_ = lean_array_fset(v_es_816_, v_j_819_, v___x_826_);
switch(lean_obj_tag(v_v_825_))
{
case 0:
{
lean_object* v_key_834_; lean_object* v_val_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_845_; 
v_key_834_ = lean_ctor_get(v_v_825_, 0);
v_val_835_ = lean_ctor_get(v_v_825_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_v_825_);
if (v_isSharedCheck_845_ == 0)
{
v___x_837_ = v_v_825_;
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_val_835_);
lean_inc(v_key_834_);
lean_dec(v_v_825_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
uint8_t v___x_839_; 
v___x_839_ = l_Lean_instBEqFVarId_beq(v_x_814_, v_key_834_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_del_object(v___x_837_);
v___x_840_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_834_, v_val_835_, v_x_814_, v_x_815_);
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
v___y_829_ = v___x_841_;
goto v___jp_828_;
}
else
{
lean_object* v___x_843_; 
lean_dec(v_val_835_);
lean_dec(v_key_834_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v_x_815_);
lean_ctor_set(v___x_837_, 0, v_x_814_);
v___x_843_ = v___x_837_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_x_814_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_x_815_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
v___y_829_ = v___x_843_;
goto v___jp_828_;
}
}
}
}
case 1:
{
lean_object* v_node_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_858_; 
v_node_846_ = lean_ctor_get(v_v_825_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_v_825_);
if (v_isSharedCheck_858_ == 0)
{
v___x_848_ = v_v_825_;
v_isShared_849_ = v_isSharedCheck_858_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_node_846_);
lean_dec(v_v_825_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_858_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
size_t v___x_850_; size_t v___x_851_; size_t v___x_852_; size_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_850_ = ((size_t)5ULL);
v___x_851_ = lean_usize_shift_right(v_x_812_, v___x_850_);
v___x_852_ = ((size_t)1ULL);
v___x_853_ = lean_usize_add(v_x_813_, v___x_852_);
v___x_854_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_node_846_, v___x_851_, v___x_853_, v_x_814_, v_x_815_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_854_);
v___x_856_ = v___x_848_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
v___y_829_ = v___x_856_;
goto v___jp_828_;
}
}
}
default: 
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_x_814_);
lean_ctor_set(v___x_859_, 1, v_x_815_);
v___y_829_ = v___x_859_;
goto v___jp_828_;
}
}
v___jp_828_:
{
lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_830_ = lean_array_fset(v_xs_x27_827_, v_j_819_, v___y_829_);
lean_dec(v_j_819_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_830_);
v___x_832_ = v___x_823_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
else
{
lean_object* v_ks_862_; lean_object* v_vs_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_881_; 
v_ks_862_ = lean_ctor_get(v_x_811_, 0);
v_vs_863_ = lean_ctor_get(v_x_811_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v_x_811_);
if (v_isSharedCheck_881_ == 0)
{
v___x_865_ = v_x_811_;
v_isShared_866_ = v_isSharedCheck_881_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_vs_863_);
lean_inc(v_ks_862_);
lean_dec(v_x_811_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_881_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_ks_862_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_vs_863_);
v___x_868_ = v_reuseFailAlloc_880_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v_newNode_869_; size_t v___x_870_; uint8_t v___x_871_; 
v_newNode_869_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(v___x_868_, v_x_814_, v_x_815_);
v___x_870_ = ((size_t)7ULL);
v___x_871_ = lean_usize_dec_le(v___x_870_, v_x_813_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_872_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_869_);
v___x_873_ = lean_unsigned_to_nat(4u);
v___x_874_ = lean_nat_dec_lt(v___x_872_, v___x_873_);
lean_dec(v___x_872_);
if (v___x_874_ == 0)
{
lean_object* v_ks_875_; lean_object* v_vs_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_ks_875_ = lean_ctor_get(v_newNode_869_, 0);
lean_inc_ref(v_ks_875_);
v_vs_876_ = lean_ctor_get(v_newNode_869_, 1);
lean_inc_ref(v_vs_876_);
lean_dec_ref(v_newNode_869_);
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0);
v___x_879_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_x_813_, v_ks_875_, v_vs_876_, v___x_877_, v___x_878_);
lean_dec_ref(v_vs_876_);
lean_dec_ref(v_ks_875_);
return v___x_879_;
}
else
{
return v_newNode_869_;
}
}
else
{
return v_newNode_869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(size_t v_depth_882_, lean_object* v_keys_883_, lean_object* v_vals_884_, lean_object* v_i_885_, lean_object* v_entries_886_){
_start:
{
lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_887_ = lean_array_get_size(v_keys_883_);
v___x_888_ = lean_nat_dec_lt(v_i_885_, v___x_887_);
if (v___x_888_ == 0)
{
lean_dec(v_i_885_);
return v_entries_886_;
}
else
{
lean_object* v_k_889_; lean_object* v_v_890_; uint64_t v___x_891_; size_t v_h_892_; size_t v___x_893_; lean_object* v___x_894_; size_t v___x_895_; size_t v___x_896_; size_t v___x_897_; size_t v_h_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_k_889_ = lean_array_fget_borrowed(v_keys_883_, v_i_885_);
v_v_890_ = lean_array_fget_borrowed(v_vals_884_, v_i_885_);
v___x_891_ = l_Lean_instHashableFVarId_hash(v_k_889_);
v_h_892_ = lean_uint64_to_usize(v___x_891_);
v___x_893_ = ((size_t)5ULL);
v___x_894_ = lean_unsigned_to_nat(1u);
v___x_895_ = ((size_t)1ULL);
v___x_896_ = lean_usize_sub(v_depth_882_, v___x_895_);
v___x_897_ = lean_usize_mul(v___x_893_, v___x_896_);
v_h_898_ = lean_usize_shift_right(v_h_892_, v___x_897_);
v___x_899_ = lean_nat_add(v_i_885_, v___x_894_);
lean_dec(v_i_885_);
lean_inc(v_v_890_);
lean_inc(v_k_889_);
v___x_900_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_entries_886_, v_h_898_, v_depth_882_, v_k_889_, v_v_890_);
v_i_885_ = v___x_899_;
v_entries_886_ = v___x_900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_depth_902_, lean_object* v_keys_903_, lean_object* v_vals_904_, lean_object* v_i_905_, lean_object* v_entries_906_){
_start:
{
size_t v_depth_boxed_907_; lean_object* v_res_908_; 
v_depth_boxed_907_ = lean_unbox_usize(v_depth_902_);
lean_dec(v_depth_902_);
v_res_908_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_depth_boxed_907_, v_keys_903_, v_vals_904_, v_i_905_, v_entries_906_);
lean_dec_ref(v_vals_904_);
lean_dec_ref(v_keys_903_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
size_t v_x_26419__boxed_914_; size_t v_x_26420__boxed_915_; lean_object* v_res_916_; 
v_x_26419__boxed_914_ = lean_unbox_usize(v_x_910_);
lean_dec(v_x_910_);
v_x_26420__boxed_915_ = lean_unbox_usize(v_x_911_);
lean_dec(v_x_911_);
v_res_916_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_909_, v_x_26419__boxed_914_, v_x_26420__boxed_915_, v_x_912_, v_x_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object* v_x_917_, lean_object* v_x_918_, lean_object* v_x_919_){
_start:
{
uint64_t v___x_920_; size_t v___x_921_; size_t v___x_922_; lean_object* v___x_923_; 
v___x_920_ = l_Lean_instHashableFVarId_hash(v_x_918_);
v___x_921_ = lean_uint64_to_usize(v___x_920_);
v___x_922_ = ((size_t)1ULL);
v___x_923_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_917_, v___x_921_, v___x_922_, v_x_918_, v_x_919_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(lean_object* v_a_924_, lean_object* v_b_925_, lean_object* v_x_926_){
_start:
{
if (lean_obj_tag(v_x_926_) == 0)
{
lean_dec(v_b_925_);
lean_dec_ref(v_a_924_);
return v_x_926_;
}
else
{
lean_object* v_key_927_; lean_object* v_value_928_; lean_object* v_tail_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_941_; 
v_key_927_ = lean_ctor_get(v_x_926_, 0);
v_value_928_ = lean_ctor_get(v_x_926_, 1);
v_tail_929_ = lean_ctor_get(v_x_926_, 2);
v_isSharedCheck_941_ = !lean_is_exclusive(v_x_926_);
if (v_isSharedCheck_941_ == 0)
{
v___x_931_ = v_x_926_;
v_isShared_932_ = v_isSharedCheck_941_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_tail_929_);
lean_inc(v_value_928_);
lean_inc(v_key_927_);
lean_dec(v_x_926_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_941_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
uint8_t v___x_933_; 
v___x_933_ = l_Lean_ExprStructEq_beq(v_key_927_, v_a_924_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_934_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_924_, v_b_925_, v_tail_929_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 2, v___x_934_);
v___x_936_ = v___x_931_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_key_927_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_value_928_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
else
{
lean_object* v___x_939_; 
lean_dec(v_value_928_);
lean_dec(v_key_927_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v_b_925_);
lean_ctor_set(v___x_931_, 0, v_a_924_);
v___x_939_ = v___x_931_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_924_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_b_925_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_tail_929_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(lean_object* v_a_942_, lean_object* v_x_943_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
uint8_t v___x_944_; 
v___x_944_ = 0;
return v___x_944_;
}
else
{
lean_object* v_key_945_; lean_object* v_tail_946_; uint8_t v___x_947_; 
v_key_945_ = lean_ctor_get(v_x_943_, 0);
v_tail_946_ = lean_ctor_get(v_x_943_, 2);
v___x_947_ = l_Lean_ExprStructEq_beq(v_key_945_, v_a_942_);
if (v___x_947_ == 0)
{
v_x_943_ = v_tail_946_;
goto _start;
}
else
{
return v___x_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg___boxed(lean_object* v_a_949_, lean_object* v_x_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_949_, v_x_950_);
lean_dec(v_x_950_);
lean_dec_ref(v_a_949_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
if (lean_obj_tag(v_x_954_) == 0)
{
return v_x_953_;
}
else
{
lean_object* v_key_955_; lean_object* v_value_956_; lean_object* v_tail_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_980_; 
v_key_955_ = lean_ctor_get(v_x_954_, 0);
v_value_956_ = lean_ctor_get(v_x_954_, 1);
v_tail_957_ = lean_ctor_get(v_x_954_, 2);
v_isSharedCheck_980_ = !lean_is_exclusive(v_x_954_);
if (v_isSharedCheck_980_ == 0)
{
v___x_959_ = v_x_954_;
v_isShared_960_ = v_isSharedCheck_980_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_tail_957_);
lean_inc(v_value_956_);
lean_inc(v_key_955_);
lean_dec(v_x_954_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_980_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; uint64_t v___x_962_; uint64_t v___x_963_; uint64_t v___x_964_; uint64_t v_fold_965_; uint64_t v___x_966_; uint64_t v___x_967_; uint64_t v___x_968_; size_t v___x_969_; size_t v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_961_ = lean_array_get_size(v_x_953_);
v___x_962_ = l_Lean_ExprStructEq_hash(v_key_955_);
v___x_963_ = 32ULL;
v___x_964_ = lean_uint64_shift_right(v___x_962_, v___x_963_);
v_fold_965_ = lean_uint64_xor(v___x_962_, v___x_964_);
v___x_966_ = 16ULL;
v___x_967_ = lean_uint64_shift_right(v_fold_965_, v___x_966_);
v___x_968_ = lean_uint64_xor(v_fold_965_, v___x_967_);
v___x_969_ = lean_uint64_to_usize(v___x_968_);
v___x_970_ = lean_usize_of_nat(v___x_961_);
v___x_971_ = ((size_t)1ULL);
v___x_972_ = lean_usize_sub(v___x_970_, v___x_971_);
v___x_973_ = lean_usize_land(v___x_969_, v___x_972_);
v___x_974_ = lean_array_uget_borrowed(v_x_953_, v___x_973_);
lean_inc(v___x_974_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 2, v___x_974_);
v___x_976_ = v___x_959_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_key_955_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_value_956_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v___x_974_);
v___x_976_ = v_reuseFailAlloc_979_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; 
v___x_977_ = lean_array_uset(v_x_953_, v___x_973_, v___x_976_);
v_x_953_ = v___x_977_;
v_x_954_ = v_tail_957_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(lean_object* v_i_981_, lean_object* v_source_982_, lean_object* v_target_983_){
_start:
{
lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_984_ = lean_array_get_size(v_source_982_);
v___x_985_ = lean_nat_dec_lt(v_i_981_, v___x_984_);
if (v___x_985_ == 0)
{
lean_dec_ref(v_source_982_);
lean_dec(v_i_981_);
return v_target_983_;
}
else
{
lean_object* v_es_986_; lean_object* v___x_987_; lean_object* v_source_988_; lean_object* v_target_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_es_986_ = lean_array_fget(v_source_982_, v_i_981_);
v___x_987_ = lean_box(0);
v_source_988_ = lean_array_fset(v_source_982_, v_i_981_, v___x_987_);
v_target_989_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(v_target_983_, v_es_986_);
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_add(v_i_981_, v___x_990_);
lean_dec(v_i_981_);
v_i_981_ = v___x_991_;
v_source_982_ = v_source_988_;
v_target_983_ = v_target_989_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(lean_object* v_data_993_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v_nbuckets_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_994_ = lean_array_get_size(v_data_993_);
v___x_995_ = lean_unsigned_to_nat(2u);
v_nbuckets_996_ = lean_nat_mul(v___x_994_, v___x_995_);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_box(0);
v___x_999_ = lean_mk_array(v_nbuckets_996_, v___x_998_);
v___x_1000_ = lean_array_propagate_mark(v_data_993_, v___x_999_);
v___x_1001_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(v___x_997_, v_data_993_, v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(lean_object* v_m_1002_, lean_object* v_a_1003_, lean_object* v_b_1004_){
_start:
{
lean_object* v_size_1005_; lean_object* v_buckets_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1049_; 
v_size_1005_ = lean_ctor_get(v_m_1002_, 0);
v_buckets_1006_ = lean_ctor_get(v_m_1002_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_m_1002_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1008_ = v_m_1002_;
v_isShared_1009_ = v_isSharedCheck_1049_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_buckets_1006_);
lean_inc(v_size_1005_);
lean_dec(v_m_1002_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1049_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; uint64_t v___x_1011_; uint64_t v___x_1012_; uint64_t v___x_1013_; uint64_t v_fold_1014_; uint64_t v___x_1015_; uint64_t v___x_1016_; uint64_t v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; size_t v___x_1022_; lean_object* v_bkt_1023_; uint8_t v___x_1024_; 
v___x_1010_ = lean_array_get_size(v_buckets_1006_);
v___x_1011_ = l_Lean_ExprStructEq_hash(v_a_1003_);
v___x_1012_ = 32ULL;
v___x_1013_ = lean_uint64_shift_right(v___x_1011_, v___x_1012_);
v_fold_1014_ = lean_uint64_xor(v___x_1011_, v___x_1013_);
v___x_1015_ = 16ULL;
v___x_1016_ = lean_uint64_shift_right(v_fold_1014_, v___x_1015_);
v___x_1017_ = lean_uint64_xor(v_fold_1014_, v___x_1016_);
v___x_1018_ = lean_uint64_to_usize(v___x_1017_);
v___x_1019_ = lean_usize_of_nat(v___x_1010_);
v___x_1020_ = ((size_t)1ULL);
v___x_1021_ = lean_usize_sub(v___x_1019_, v___x_1020_);
v___x_1022_ = lean_usize_land(v___x_1018_, v___x_1021_);
v_bkt_1023_ = lean_array_uget_borrowed(v_buckets_1006_, v___x_1022_);
v___x_1024_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_1003_, v_bkt_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v_size_x27_1026_; lean_object* v___x_1027_; lean_object* v_buckets_x27_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1025_ = lean_unsigned_to_nat(1u);
v_size_x27_1026_ = lean_nat_add(v_size_1005_, v___x_1025_);
lean_dec(v_size_1005_);
lean_inc(v_bkt_1023_);
v___x_1027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1027_, 0, v_a_1003_);
lean_ctor_set(v___x_1027_, 1, v_b_1004_);
lean_ctor_set(v___x_1027_, 2, v_bkt_1023_);
v_buckets_x27_1028_ = lean_array_uset(v_buckets_1006_, v___x_1022_, v___x_1027_);
v___x_1029_ = lean_unsigned_to_nat(4u);
v___x_1030_ = lean_nat_mul(v_size_x27_1026_, v___x_1029_);
v___x_1031_ = lean_unsigned_to_nat(3u);
v___x_1032_ = lean_nat_div(v___x_1030_, v___x_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_array_get_size(v_buckets_x27_1028_);
v___x_1034_ = lean_nat_dec_le(v___x_1032_, v___x_1033_);
lean_dec(v___x_1032_);
if (v___x_1034_ == 0)
{
lean_object* v_val_1035_; lean_object* v___x_1037_; 
v_val_1035_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(v_buckets_x27_1028_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v_val_1035_);
lean_ctor_set(v___x_1008_, 0, v_size_x27_1026_);
v___x_1037_ = v___x_1008_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_size_x27_1026_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_val_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
else
{
lean_object* v___x_1040_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v_buckets_x27_1028_);
lean_ctor_set(v___x_1008_, 0, v_size_x27_1026_);
v___x_1040_ = v___x_1008_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_size_x27_1026_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_buckets_x27_1028_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
else
{
lean_object* v___x_1042_; lean_object* v_buckets_x27_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
lean_inc(v_bkt_1023_);
v___x_1042_ = lean_box(0);
v_buckets_x27_1043_ = lean_array_uset(v_buckets_1006_, v___x_1022_, v___x_1042_);
v___x_1044_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_1003_, v_b_1004_, v_bkt_1023_);
v___x_1045_ = lean_array_uset(v_buckets_x27_1043_, v___x_1022_, v___x_1044_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v___x_1045_);
v___x_1047_ = v___x_1008_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_size_1005_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(lean_object* v_a_1050_, lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_box(0);
return v___x_1052_;
}
else
{
lean_object* v_key_1053_; lean_object* v_value_1054_; lean_object* v_tail_1055_; uint8_t v___x_1056_; 
v_key_1053_ = lean_ctor_get(v_x_1051_, 0);
v_value_1054_ = lean_ctor_get(v_x_1051_, 1);
v_tail_1055_ = lean_ctor_get(v_x_1051_, 2);
v___x_1056_ = l_Lean_ExprStructEq_beq(v_key_1053_, v_a_1050_);
if (v___x_1056_ == 0)
{
v_x_1051_ = v_tail_1055_;
goto _start;
}
else
{
lean_object* v___x_1058_; 
lean_inc(v_value_1054_);
v___x_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1058_, 0, v_value_1054_);
return v___x_1058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___boxed(lean_object* v_a_1059_, lean_object* v_x_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1059_, v_x_1060_);
lean_dec(v_x_1060_);
lean_dec_ref(v_a_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(lean_object* v_m_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_buckets_1064_; lean_object* v___x_1065_; uint64_t v___x_1066_; uint64_t v___x_1067_; uint64_t v___x_1068_; uint64_t v_fold_1069_; uint64_t v___x_1070_; uint64_t v___x_1071_; uint64_t v___x_1072_; size_t v___x_1073_; size_t v___x_1074_; size_t v___x_1075_; size_t v___x_1076_; size_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_buckets_1064_ = lean_ctor_get(v_m_1062_, 1);
v___x_1065_ = lean_array_get_size(v_buckets_1064_);
v___x_1066_ = l_Lean_ExprStructEq_hash(v_a_1063_);
v___x_1067_ = 32ULL;
v___x_1068_ = lean_uint64_shift_right(v___x_1066_, v___x_1067_);
v_fold_1069_ = lean_uint64_xor(v___x_1066_, v___x_1068_);
v___x_1070_ = 16ULL;
v___x_1071_ = lean_uint64_shift_right(v_fold_1069_, v___x_1070_);
v___x_1072_ = lean_uint64_xor(v_fold_1069_, v___x_1071_);
v___x_1073_ = lean_uint64_to_usize(v___x_1072_);
v___x_1074_ = lean_usize_of_nat(v___x_1065_);
v___x_1075_ = ((size_t)1ULL);
v___x_1076_ = lean_usize_sub(v___x_1074_, v___x_1075_);
v___x_1077_ = lean_usize_land(v___x_1073_, v___x_1076_);
v___x_1078_ = lean_array_uget_borrowed(v_buckets_1064_, v___x_1077_);
v___x_1079_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1063_, v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___boxed(lean_object* v_m_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_m_1080_, v_a_1081_);
lean_dec_ref(v_a_1081_);
lean_dec_ref(v_m_1080_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0(lean_object* v_proof_1083_, uint8_t v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1088_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
v___x_1091_ = lean_infer_type(v_proof_1083_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0___boxed(lean_object* v_proof_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
uint8_t v___y_26838__boxed_1100_; lean_object* v_res_1101_; 
v___y_26838__boxed_1100_ = lean_unbox(v___y_1093_);
v_res_1101_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0(v_proof_1092_, v___y_26838__boxed_1100_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(lean_object* v_x_1102_, uint8_t v_isExporting_1103_, uint8_t v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_env_1112_; lean_object* v___x_1113_; uint8_t v_isModule_1114_; 
v___x_1111_ = lean_st_ref_get(v___y_1109_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = l_Lean_Environment_header(v_env_1112_);
v_isModule_1114_ = lean_ctor_get_uint8(v___x_1113_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1113_);
if (v_isModule_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec_ref(v_env_1112_);
v___x_1115_ = lean_box(v___y_1104_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1105_);
v___x_1116_ = lean_apply_7(v_x_1102_, v___x_1115_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, lean_box(0));
return v___x_1116_;
}
else
{
uint8_t v_isExporting_1117_; 
v_isExporting_1117_ = lean_ctor_get_uint8(v_env_1112_, sizeof(void*)*8);
lean_dec_ref(v_env_1112_);
if (v_isExporting_1103_ == 0)
{
if (v_isExporting_1117_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_box(v___y_1104_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1105_);
v___x_1185_ = lean_apply_7(v_x_1102_, v___x_1184_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, lean_box(0));
return v___x_1185_;
}
else
{
goto v___jp_1118_;
}
}
else
{
if (v_isExporting_1117_ == 0)
{
goto v___jp_1118_;
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_box(v___y_1104_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1105_);
v___x_1187_ = lean_apply_7(v_x_1102_, v___x_1186_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, lean_box(0));
return v___x_1187_;
}
}
v___jp_1118_:
{
lean_object* v___x_1119_; lean_object* v_env_1120_; lean_object* v_nextMacroScope_1121_; lean_object* v_ngen_1122_; lean_object* v_auxDeclNGen_1123_; lean_object* v_traceState_1124_; lean_object* v_messages_1125_; lean_object* v_infoState_1126_; lean_object* v_snapshotTasks_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1182_; 
v___x_1119_ = lean_st_ref_take(v___y_1109_);
v_env_1120_ = lean_ctor_get(v___x_1119_, 0);
v_nextMacroScope_1121_ = lean_ctor_get(v___x_1119_, 1);
v_ngen_1122_ = lean_ctor_get(v___x_1119_, 2);
v_auxDeclNGen_1123_ = lean_ctor_get(v___x_1119_, 3);
v_traceState_1124_ = lean_ctor_get(v___x_1119_, 4);
v_messages_1125_ = lean_ctor_get(v___x_1119_, 6);
v_infoState_1126_ = lean_ctor_get(v___x_1119_, 7);
v_snapshotTasks_1127_ = lean_ctor_get(v___x_1119_, 8);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v___x_1119_, 5);
lean_dec(v_unused_1183_);
v___x_1129_ = v___x_1119_;
v_isShared_1130_ = v_isSharedCheck_1182_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_snapshotTasks_1127_);
lean_inc(v_infoState_1126_);
lean_inc(v_messages_1125_);
lean_inc(v_traceState_1124_);
lean_inc(v_auxDeclNGen_1123_);
lean_inc(v_ngen_1122_);
lean_inc(v_nextMacroScope_1121_);
lean_inc(v_env_1120_);
lean_dec(v___x_1119_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1182_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1131_ = l_Lean_Environment_setExporting(v_env_1120_, v_isExporting_1103_);
v___x_1132_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 5, v___x_1132_);
lean_ctor_set(v___x_1129_, 0, v___x_1131_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_nextMacroScope_1121_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_ngen_1122_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v_auxDeclNGen_1123_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v_traceState_1124_);
lean_ctor_set(v_reuseFailAlloc_1181_, 5, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1181_, 6, v_messages_1125_);
lean_ctor_set(v_reuseFailAlloc_1181_, 7, v_infoState_1126_);
lean_ctor_set(v_reuseFailAlloc_1181_, 8, v_snapshotTasks_1127_);
v___x_1134_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_mctx_1137_; lean_object* v_zetaDeltaFVarIds_1138_; lean_object* v_postponed_1139_; lean_object* v_diag_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1179_; 
v___x_1135_ = lean_st_ref_put(v___y_1109_, v___x_1134_);
v___x_1136_ = lean_st_ref_take(v___y_1107_);
v_mctx_1137_ = lean_ctor_get(v___x_1136_, 0);
v_zetaDeltaFVarIds_1138_ = lean_ctor_get(v___x_1136_, 2);
v_postponed_1139_ = lean_ctor_get(v___x_1136_, 3);
v_diag_1140_ = lean_ctor_get(v___x_1136_, 4);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; 
v_unused_1180_ = lean_ctor_get(v___x_1136_, 1);
lean_dec(v_unused_1180_);
v___x_1142_ = v___x_1136_;
v_isShared_1143_ = v_isSharedCheck_1179_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_diag_1140_);
lean_inc(v_postponed_1139_);
lean_inc(v_zetaDeltaFVarIds_1138_);
lean_inc(v_mctx_1137_);
lean_dec(v___x_1136_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1179_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1144_);
v___x_1146_ = v___x_1142_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_mctx_1137_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1178_, 2, v_zetaDeltaFVarIds_1138_);
lean_ctor_set(v_reuseFailAlloc_1178_, 3, v_postponed_1139_);
lean_ctor_set(v_reuseFailAlloc_1178_, 4, v_diag_1140_);
v___x_1146_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v_r_1149_; 
v___x_1147_ = lean_st_ref_put(v___y_1107_, v___x_1146_);
v___x_1148_ = lean_box(v___y_1104_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1105_);
v_r_1149_ = lean_apply_7(v_x_1102_, v___x_1148_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, lean_box(0));
if (lean_obj_tag(v_r_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1166_; 
v_a_1150_ = lean_ctor_get(v_r_1149_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_r_1149_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1152_ = v_r_1149_;
v_isShared_1153_ = v_isSharedCheck_1166_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v_r_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1166_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
lean_inc(v_a_1150_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 1);
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
v___x_1156_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_1109_, v_isExporting_1117_, v___x_1132_, v___y_1107_, v___x_1144_, v___x_1155_);
lean_dec_ref(v___x_1155_);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v___x_1156_, 0);
lean_dec(v_unused_1164_);
v___x_1158_ = v___x_1156_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_dec(v___x_1156_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v_a_1150_);
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1150_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
v_a_1167_ = lean_ctor_get(v_r_1149_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v_r_1149_, 1);
v___x_1168_ = lean_box(0);
v___x_1169_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_1109_, v_isExporting_1117_, v___x_1132_, v___y_1107_, v___x_1144_, v___x_1168_);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; 
v_unused_1177_ = lean_ctor_get(v___x_1169_, 0);
lean_dec(v_unused_1177_);
v___x_1171_ = v___x_1169_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_dec(v___x_1169_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
lean_ctor_set_tag(v___x_1171_, 1);
lean_ctor_set(v___x_1171_, 0, v_a_1167_);
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1167_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg___boxed(lean_object* v_x_1188_, lean_object* v_isExporting_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
uint8_t v_isExporting_boxed_1197_; uint8_t v___y_26874__boxed_1198_; lean_object* v_res_1199_; 
v_isExporting_boxed_1197_ = lean_unbox(v_isExporting_1189_);
v___y_26874__boxed_1198_ = lean_unbox(v___y_1190_);
v_res_1199_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(v_x_1188_, v_isExporting_boxed_1197_, v___y_26874__boxed_1198_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(lean_object* v_x_1200_, uint8_t v_when_1201_, uint8_t v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
if (v_when_1201_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_box(v___y_1202_);
lean_inc(v___y_1207_);
lean_inc_ref(v___y_1206_);
lean_inc(v___y_1205_);
lean_inc_ref(v___y_1204_);
lean_inc(v___y_1203_);
v___x_1210_ = lean_apply_7(v_x_1200_, v___x_1209_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, lean_box(0));
return v___x_1210_;
}
else
{
uint8_t v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = 0;
v___x_1212_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(v_x_1200_, v___x_1211_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg___boxed(lean_object* v_x_1213_, lean_object* v_when_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
uint8_t v_when_boxed_1222_; uint8_t v___y_27023__boxed_1223_; lean_object* v_res_1224_; 
v_when_boxed_1222_ = lean_unbox(v_when_1214_);
v___y_27023__boxed_1223_ = lean_unbox(v___y_1215_);
v_res_1224_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(v_x_1213_, v_when_boxed_1222_, v___y_27023__boxed_1223_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object* v_proof_1225_, uint8_t v_cache_1226_, lean_object* v_postprocessType_1227_, uint8_t v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___f_1235_; uint8_t v___x_1236_; lean_object* v___x_1237_; 
lean_inc_ref(v_proof_1225_);
v___f_1235_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1235_, 0, v_proof_1225_);
v___x_1236_ = 1;
v___x_1237_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(v___f_1235_, v___x_1236_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1239_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v___x_1239_ = l_Lean_Core_betaReduce(v_a_1238_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1241_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = l_Lean_Meta_zetaReduce(v_a_1240_, v___x_1236_, v___x_1236_, v___x_1236_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = lean_box(v___y_1228_);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
v___x_1244_ = lean_apply_8(v_postprocessType_1227_, v_a_1242_, v___x_1243_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, lean_box(0));
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; uint8_t v___y_1247_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
if (v_cache_1226_ == 0)
{
v___y_1247_ = v_cache_1226_;
goto v___jp_1246_;
}
else
{
uint8_t v___x_1250_; 
v___x_1250_ = l_Lean_Expr_hasSorry(v_proof_1225_);
if (v___x_1250_ == 0)
{
v___y_1247_ = v_cache_1226_;
goto v___jp_1246_;
}
else
{
uint8_t v___x_1251_; 
v___x_1251_ = 0;
v___y_1247_ = v___x_1251_;
goto v___jp_1246_;
}
}
v___jp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = l_Lean_Meta_mkAuxTheorem(v_a_1245_, v_proof_1225_, v___x_1236_, v___x_1248_, v___y_1247_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
return v___x_1249_;
}
}
else
{
lean_dec_ref(v_proof_1225_);
return v___x_1244_;
}
}
else
{
lean_dec_ref(v_postprocessType_1227_);
lean_dec_ref(v_proof_1225_);
return v___x_1241_;
}
}
else
{
lean_dec_ref(v_postprocessType_1227_);
lean_dec_ref(v_proof_1225_);
return v___x_1239_;
}
}
else
{
lean_dec_ref(v_postprocessType_1227_);
lean_dec_ref(v_proof_1225_);
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object* v_proof_1252_, lean_object* v_cache_1253_, lean_object* v_postprocessType_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
uint8_t v_cache_boxed_1262_; uint8_t v___y_27052__boxed_1263_; lean_object* v_res_1264_; 
v_cache_boxed_1262_ = lean_unbox(v_cache_1253_);
v___y_27052__boxed_1263_ = lean_unbox(v___y_1255_);
v_res_1264_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_proof_1252_, v_cache_boxed_1262_, v_postprocessType_1254_, v___y_27052__boxed_1263_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object* v_as_1265_, size_t v_sz_1266_, size_t v_i_1267_, lean_object* v_b_1268_, uint8_t v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_a_1277_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; uint8_t v___x_1290_; 
v___x_1290_ = lean_usize_dec_lt(v_i_1267_, v_sz_1266_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v_b_1268_);
return v___x_1291_;
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1293_; lean_object* v_localDecl_1295_; lean_object* v___x_1303_; 
v_a_1292_ = lean_array_uget_borrowed(v_as_1265_, v_i_1267_);
v___x_1293_ = l_Lean_Expr_fvarId_x21(v_a_1292_);
lean_inc(v___x_1293_);
v___x_1303_ = l_Lean_FVarId_getDecl___redArg(v___x_1293_, v___y_1271_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = l_Lean_LocalDecl_type(v_a_1304_);
v___x_1306_ = l_Lean_Meta_AbstractNestedProofs_visit(v___x_1305_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = l_Lean_LocalDecl_setType(v_a_1304_, v_a_1307_);
v___x_1309_ = l_Lean_LocalDecl_value_x3f(v___x_1308_, v___x_1290_);
if (lean_obj_tag(v___x_1309_) == 0)
{
v_localDecl_1295_ = v___x_1308_;
goto v___jp_1294_;
}
else
{
lean_object* v_val_1310_; lean_object* v___x_1311_; 
v_val_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_val_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1311_ = l_Lean_Meta_AbstractNestedProofs_visit(v_val_1310_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1313_ = l_Lean_LocalDecl_setValue(v___x_1308_, v_a_1312_);
v_localDecl_1295_ = v___x_1313_;
goto v___jp_1294_;
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v___x_1308_);
lean_dec(v___x_1293_);
lean_dec_ref(v_b_1268_);
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
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v_a_1304_);
lean_dec(v___x_1293_);
lean_dec_ref(v_b_1268_);
v_a_1322_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1306_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1306_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v___x_1293_);
lean_dec_ref(v_b_1268_);
v_a_1330_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1303_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1303_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
v___jp_1294_:
{
lean_object* v_fvarIdToDecl_1296_; lean_object* v_decls_1297_; lean_object* v_auxDeclToFullName_1298_; lean_object* v___x_1299_; 
v_fvarIdToDecl_1296_ = lean_ctor_get(v_b_1268_, 0);
v_decls_1297_ = lean_ctor_get(v_b_1268_, 1);
v_auxDeclToFullName_1298_ = lean_ctor_get(v_b_1268_, 2);
lean_inc_ref(v_b_1268_);
v___x_1299_ = lean_local_ctx_find(v_b_1268_, v___x_1293_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_dec_ref(v_localDecl_1295_);
v_a_1277_ = v_b_1268_;
goto v___jp_1276_;
}
else
{
lean_object* v_index_1300_; lean_object* v_fvarId_1301_; lean_object* v___x_1302_; 
lean_inc(v_auxDeclToFullName_1298_);
lean_inc_ref(v_decls_1297_);
lean_inc_ref(v_fvarIdToDecl_1296_);
lean_dec_ref_known(v___x_1299_, 1);
lean_dec_ref(v_b_1268_);
v_index_1300_ = lean_ctor_get(v_localDecl_1295_, 0);
lean_inc(v_index_1300_);
v_fvarId_1301_ = lean_ctor_get(v_localDecl_1295_, 1);
lean_inc_ref(v_localDecl_1295_);
lean_inc(v_fvarId_1301_);
v___x_1302_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_fvarIdToDecl_1296_, v_fvarId_1301_, v_localDecl_1295_);
v___y_1282_ = v_localDecl_1295_;
v___y_1283_ = v_auxDeclToFullName_1298_;
v___y_1284_ = v_decls_1297_;
v___y_1285_ = v___x_1302_;
v___y_1286_ = v_index_1300_;
goto v___jp_1281_;
}
}
}
v___jp_1276_:
{
size_t v___x_1278_; size_t v___x_1279_; 
v___x_1278_ = ((size_t)1ULL);
v___x_1279_ = lean_usize_add(v_i_1267_, v___x_1278_);
v_i_1267_ = v___x_1279_;
v_b_1268_ = v_a_1277_;
goto _start;
}
v___jp_1281_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___y_1282_);
v___x_1288_ = l_Lean_PersistentArray_set___redArg(v___y_1284_, v___y_1286_, v___x_1287_);
lean_dec(v___y_1286_);
v___x_1289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1289_, 0, v___y_1285_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
lean_ctor_set(v___x_1289_, 2, v___y_1283_);
v_a_1277_ = v___x_1289_;
goto v___jp_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object* v_xs_1338_, lean_object* v_k_1339_, uint8_t v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_lctx_1347_; lean_object* v_localInstances_1348_; size_t v_sz_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v_lctx_1347_ = lean_ctor_get(v___y_1342_, 2);
v_localInstances_1348_ = lean_ctor_get(v___y_1342_, 3);
v_sz_1349_ = lean_array_size(v_xs_1338_);
v___x_1350_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1347_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_xs_1338_, v_sz_1349_, v___x_1350_, v_lctx_1347_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1353_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
lean_inc_ref(v_localInstances_1348_);
v___x_1353_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_a_1352_, v_localInstances_1348_, v_k_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
return v___x_1353_;
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_k_1339_);
v_a_1354_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1351_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1351_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object* v_xs_1362_, lean_object* v_k_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
uint8_t v___y_27163__boxed_1371_; lean_object* v_res_1372_; 
v___y_27163__boxed_1371_ = lean_unbox(v___y_1364_);
v_res_1372_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(v_xs_1362_, v_k_1363_, v___y_27163__boxed_1371_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v_xs_1362_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object* v_e_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
uint8_t v_a_boxed_1382_; lean_object* v_res_1383_; 
v_a_boxed_1382_ = lean_unbox(v_a_1375_);
v_res_1383_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1374_, v_a_boxed_1382_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object* v___y_1384_, lean_object* v___f_1385_, lean_object* v_xs_1386_, lean_object* v_b_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v___y_27113__boxed_1395_; uint8_t v___y_27115__boxed_1396_; lean_object* v_res_1397_; 
v___y_27113__boxed_1395_ = lean_unbox(v___y_1384_);
v___y_27115__boxed_1396_ = lean_unbox(v___y_1388_);
v_res_1397_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(v___y_27113__boxed_1395_, v___f_1385_, v_xs_1386_, v_b_1387_, v___y_27115__boxed_1396_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object* v_b_1398_, lean_object* v_xs_1399_, uint8_t v___y_1400_, uint8_t v___x_1401_, uint8_t v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1398_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v___x_1411_ = 1;
v___x_1412_ = l_Lean_Meta_mkForallFVars(v_xs_1399_, v_a_1410_, v___y_1400_, v___x_1401_, v___x_1401_, v___x_1411_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1412_;
}
else
{
return v___x_1409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object* v_b_1413_, lean_object* v_xs_1414_, lean_object* v___y_1415_, lean_object* v___x_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v___y_27149__boxed_1424_; uint8_t v___x_27150__boxed_1425_; uint8_t v___y_27151__boxed_1426_; lean_object* v_res_1427_; 
v___y_27149__boxed_1424_ = lean_unbox(v___y_1415_);
v___x_27150__boxed_1425_ = lean_unbox(v___x_1416_);
v___y_27151__boxed_1426_ = lean_unbox(v___y_1417_);
v_res_1427_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(v_b_1413_, v_xs_1414_, v___y_27149__boxed_1424_, v___x_27150__boxed_1425_, v___y_27151__boxed_1426_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v_xs_1414_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t v___y_1428_, uint8_t v___x_1429_, lean_object* v___f_1430_, lean_object* v_xs_1431_, lean_object* v_b_1432_, uint8_t v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1440_ = lean_box(v___y_1428_);
v___x_1441_ = lean_box(v___x_1429_);
lean_inc_ref(v_xs_1431_);
v___f_1442_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1442_, 0, v_b_1432_);
lean_closure_set(v___f_1442_, 1, v_xs_1431_);
lean_closure_set(v___f_1442_, 2, v___x_1440_);
lean_closure_set(v___f_1442_, 3, v___x_1441_);
v___x_1443_ = lean_box(v___y_1433_);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc(v___y_1434_);
v___x_1444_ = lean_apply_9(v___f_1430_, v_xs_1431_, v___f_1442_, v___x_1443_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, lean_box(0));
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object* v___y_1445_, lean_object* v___x_1446_, lean_object* v___f_1447_, lean_object* v_xs_1448_, lean_object* v_b_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
uint8_t v___y_27124__boxed_1457_; uint8_t v___x_27125__boxed_1458_; uint8_t v___y_27127__boxed_1459_; lean_object* v_res_1460_; 
v___y_27124__boxed_1457_ = lean_unbox(v___y_1445_);
v___x_27125__boxed_1458_ = lean_unbox(v___x_1446_);
v___y_27127__boxed_1459_ = lean_unbox(v___y_1450_);
v_res_1460_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(v___y_27124__boxed_1457_, v___x_27125__boxed_1458_, v___f_1447_, v_xs_1448_, v_b_1449_, v___y_27127__boxed_1459_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t v_sz_1461_, size_t v_i_1462_, lean_object* v_bs_1463_, uint8_t v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
uint8_t v___x_1471_; 
v___x_1471_ = lean_usize_dec_lt(v_i_1462_, v_sz_1461_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v_bs_1463_);
return v___x_1472_;
}
else
{
lean_object* v_v_1473_; lean_object* v___x_1474_; lean_object* v_bs_x27_1475_; lean_object* v___x_1476_; 
v_v_1473_ = lean_array_uget(v_bs_1463_, v_i_1462_);
v___x_1474_ = lean_unsigned_to_nat(0u);
v_bs_x27_1475_ = lean_array_uset(v_bs_1463_, v_i_1462_, v___x_1474_);
v___x_1476_ = l_Lean_Meta_AbstractNestedProofs_visit(v_v_1473_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; size_t v___x_1478_; size_t v___x_1479_; lean_object* v___x_1480_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v___x_1478_ = ((size_t)1ULL);
v___x_1479_ = lean_usize_add(v_i_1462_, v___x_1478_);
v___x_1480_ = lean_array_uset(v_bs_x27_1475_, v_i_1462_, v_a_1477_);
v_i_1462_ = v___x_1479_;
v_bs_1463_ = v___x_1480_;
goto _start;
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v_bs_x27_1475_);
v_a_1482_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1476_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1476_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object* v_x_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, uint8_t v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
if (lean_obj_tag(v_x_1490_) == 5)
{
lean_object* v_fn_1500_; lean_object* v_arg_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_fn_1500_ = lean_ctor_get(v_x_1490_, 0);
lean_inc_ref(v_fn_1500_);
v_arg_1501_ = lean_ctor_get(v_x_1490_, 1);
lean_inc_ref(v_arg_1501_);
lean_dec_ref_known(v_x_1490_, 2);
v___x_1502_ = lean_array_set(v_x_1491_, v_x_1492_, v_arg_1501_);
v___x_1503_ = lean_unsigned_to_nat(1u);
v___x_1504_ = lean_nat_sub(v_x_1492_, v___x_1503_);
lean_dec(v_x_1492_);
v_x_1490_ = v_fn_1500_;
v_x_1491_ = v___x_1502_;
v_x_1492_ = v___x_1504_;
goto _start;
}
else
{
lean_object* v___x_1506_; 
lean_dec(v_x_1492_);
v___x_1506_ = l_Lean_Meta_AbstractNestedProofs_visit(v_x_1490_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; size_t v_sz_1508_; size_t v___x_1509_; lean_object* v___x_1510_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v_sz_1508_ = lean_array_size(v_x_1491_);
v___x_1509_ = ((size_t)0ULL);
v___x_1510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_1508_, v___x_1509_, v_x_1491_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1519_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1515_ = l_Lean_mkAppN(v_a_1507_, v_a_1511_);
lean_dec(v_a_1511_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1515_);
v___x_1517_ = v___x_1513_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_a_1507_);
v_a_1520_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1510_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1510_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
else
{
lean_dec_ref(v_x_1491_);
return v___x_1506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object* v_e_1528_, uint8_t v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_a_1537_; lean_object* v___y_1543_; lean_object* v___f_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___f_1545_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed), 9, 0);
v___x_1546_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_visit___closed__0));
v___x_1547_ = l_Lean_Core_checkSystem(v___x_1546_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1612_; 
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v___x_1547_, 0);
lean_dec(v_unused_1613_);
v___x_1549_ = v___x_1547_;
v_isShared_1550_ = v_isSharedCheck_1612_;
goto v_resetjp_1548_;
}
else
{
lean_dec(v___x_1547_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1612_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
uint8_t v___x_1551_; 
v___x_1551_ = l_Lean_Expr_isAtomic(v_e_1528_);
if (v___x_1551_ == 0)
{
uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = 1;
v___x_1553_ = lean_st_ref_get(v_a_1530_);
v___x_1554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v___x_1553_, v_e_1528_);
lean_dec(v___x_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v___x_1555_; 
lean_del_object(v___x_1549_);
lean_inc_ref(v_e_1528_);
v___x_1555_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_1528_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; uint8_t v___y_1561_; uint8_t v___x_1595_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1595_ = lean_unbox(v_a_1556_);
lean_dec(v_a_1556_);
if (v___x_1595_ == 0)
{
v___y_1561_ = v___x_1551_;
goto v___jp_1560_;
}
else
{
uint8_t v___x_1596_; 
v___x_1596_ = l_Lean_Expr_hasSorry(v_e_1528_);
if (v___x_1596_ == 0)
{
lean_dec_ref(v___f_1545_);
goto v___jp_1557_;
}
else
{
v___y_1561_ = v___x_1551_;
goto v___jp_1560_;
}
}
v___jp_1557_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___boxed), 8, 0);
lean_inc_ref(v_e_1528_);
v___x_1559_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_e_1528_, v_a_1529_, v___x_1558_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
v___y_1543_ = v___x_1559_;
goto v___jp_1542_;
}
v___jp_1560_:
{
if (v___y_1561_ == 0)
{
switch(lean_obj_tag(v_e_1528_))
{
case 6:
{
lean_object* v___x_1562_; lean_object* v___f_1563_; lean_object* v___x_1564_; 
v___x_1562_ = lean_box(v___y_1561_);
v___f_1563_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1563_, 0, v___x_1562_);
lean_closure_set(v___f_1563_, 1, v___f_1545_);
lean_inc_ref(v_e_1528_);
v___x_1564_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1528_, v___f_1563_, v___y_1561_, v___x_1552_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
v___y_1543_ = v___x_1564_;
goto v___jp_1542_;
}
case 8:
{
lean_object* v___x_1565_; lean_object* v___f_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_box(v___y_1561_);
v___f_1566_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1566_, 0, v___x_1565_);
lean_closure_set(v___f_1566_, 1, v___f_1545_);
lean_inc_ref(v_e_1528_);
v___x_1567_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1528_, v___f_1566_, v___y_1561_, v___x_1552_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
v___y_1543_ = v___x_1567_;
goto v___jp_1542_;
}
case 7:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___f_1570_; lean_object* v___x_1571_; 
v___x_1568_ = lean_box(v___y_1561_);
v___x_1569_ = lean_box(v___x_1552_);
v___f_1570_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed), 12, 3);
lean_closure_set(v___f_1570_, 0, v___x_1568_);
lean_closure_set(v___f_1570_, 1, v___x_1569_);
lean_closure_set(v___f_1570_, 2, v___f_1545_);
lean_inc_ref(v_e_1528_);
v___x_1571_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_e_1528_, v___f_1570_, v___y_1561_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
v___y_1543_ = v___x_1571_;
goto v___jp_1542_;
}
case 10:
{
lean_object* v_data_1572_; lean_object* v_expr_1573_; lean_object* v___x_1574_; 
lean_dec_ref(v___f_1545_);
v_data_1572_ = lean_ctor_get(v_e_1528_, 0);
v_expr_1573_ = lean_ctor_get(v_e_1528_, 1);
lean_inc_ref(v_expr_1573_);
v___x_1574_ = l_Lean_Meta_AbstractNestedProofs_visit(v_expr_1573_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; size_t v___x_1576_; size_t v___x_1577_; uint8_t v___x_1578_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v___x_1576_ = lean_ptr_addr(v_expr_1573_);
v___x_1577_ = lean_ptr_addr(v_a_1575_);
v___x_1578_ = lean_usize_dec_eq(v___x_1576_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; 
lean_inc(v_data_1572_);
v___x_1579_ = l_Lean_Expr_mdata___override(v_data_1572_, v_a_1575_);
v_a_1537_ = v___x_1579_;
goto v___jp_1536_;
}
else
{
lean_dec(v_a_1575_);
lean_inc_ref(v_e_1528_);
v_a_1537_ = v_e_1528_;
goto v___jp_1536_;
}
}
else
{
v___y_1543_ = v___x_1574_;
goto v___jp_1542_;
}
}
case 11:
{
lean_object* v_typeName_1580_; lean_object* v_idx_1581_; lean_object* v_struct_1582_; lean_object* v___x_1583_; 
lean_dec_ref(v___f_1545_);
v_typeName_1580_ = lean_ctor_get(v_e_1528_, 0);
v_idx_1581_ = lean_ctor_get(v_e_1528_, 1);
v_struct_1582_ = lean_ctor_get(v_e_1528_, 2);
lean_inc_ref(v_struct_1582_);
v___x_1583_ = l_Lean_Meta_AbstractNestedProofs_visit(v_struct_1582_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; size_t v___x_1585_; size_t v___x_1586_; uint8_t v___x_1587_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = lean_ptr_addr(v_struct_1582_);
v___x_1586_ = lean_ptr_addr(v_a_1584_);
v___x_1587_ = lean_usize_dec_eq(v___x_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
lean_inc(v_idx_1581_);
lean_inc(v_typeName_1580_);
v___x_1588_ = l_Lean_Expr_proj___override(v_typeName_1580_, v_idx_1581_, v_a_1584_);
v_a_1537_ = v___x_1588_;
goto v___jp_1536_;
}
else
{
lean_dec(v_a_1584_);
lean_inc_ref(v_e_1528_);
v_a_1537_ = v_e_1528_;
goto v___jp_1536_;
}
}
else
{
v___y_1543_ = v___x_1583_;
goto v___jp_1542_;
}
}
case 5:
{
lean_object* v_dummy_1589_; lean_object* v_nargs_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec_ref(v___f_1545_);
v_dummy_1589_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_1590_ = l_Lean_Expr_getAppNumArgs(v_e_1528_);
lean_inc(v_nargs_1590_);
v___x_1591_ = lean_mk_array(v_nargs_1590_, v_dummy_1589_);
v___x_1592_ = lean_unsigned_to_nat(1u);
v___x_1593_ = lean_nat_sub(v_nargs_1590_, v___x_1592_);
lean_dec(v_nargs_1590_);
lean_inc_ref(v_e_1528_);
v___x_1594_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_e_1528_, v___x_1591_, v___x_1593_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
v___y_1543_ = v___x_1594_;
goto v___jp_1542_;
}
default: 
{
lean_dec_ref(v___f_1545_);
lean_inc_ref(v_e_1528_);
v_a_1537_ = v_e_1528_;
goto v___jp_1536_;
}
}
}
else
{
lean_dec_ref(v___f_1545_);
goto v___jp_1557_;
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v___f_1545_);
lean_dec_ref(v_e_1528_);
v_a_1597_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1555_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1555_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
lean_object* v_val_1605_; lean_object* v___x_1607_; 
lean_dec_ref(v___f_1545_);
lean_dec_ref(v_e_1528_);
v_val_1605_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1605_);
lean_dec_ref_known(v___x_1554_, 1);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v_val_1605_);
v___x_1607_ = v___x_1549_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_val_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
else
{
lean_object* v___x_1610_; 
lean_dec_ref(v___f_1545_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v_e_1528_);
v___x_1610_ = v___x_1549_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_e_1528_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec_ref(v___f_1545_);
lean_dec_ref(v_e_1528_);
v_a_1614_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1547_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1547_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
v___jp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1538_ = lean_st_ref_take(v_a_1530_);
lean_inc_ref(v_a_1537_);
v___x_1539_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v___x_1538_, v_e_1528_, v_a_1537_);
v___x_1540_ = lean_st_ref_put(v_a_1530_, v___x_1539_);
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v_a_1537_);
return v___x_1541_;
}
v___jp_1542_:
{
if (lean_obj_tag(v___y_1543_) == 0)
{
lean_object* v_a_1544_; 
v_a_1544_ = lean_ctor_get(v___y_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___y_1543_, 1);
v_a_1537_ = v_a_1544_;
goto v___jp_1536_;
}
else
{
lean_dec_ref(v_e_1528_);
return v___y_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object* v_b_1622_, lean_object* v_xs_1623_, uint8_t v___y_1624_, uint8_t v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1622_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___x_1634_ = 1;
v___x_1635_ = l_Lean_Meta_mkLambdaFVars(v_xs_1623_, v_a_1633_, v___y_1624_, v___y_1624_, v___y_1624_, v___y_1624_, v___x_1634_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1635_;
}
else
{
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object* v_b_1636_, lean_object* v_xs_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v___y_27136__boxed_1646_; uint8_t v___y_27137__boxed_1647_; lean_object* v_res_1648_; 
v___y_27136__boxed_1646_ = lean_unbox(v___y_1638_);
v___y_27137__boxed_1647_ = lean_unbox(v___y_1639_);
v_res_1648_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(v_b_1636_, v_xs_1637_, v___y_27136__boxed_1646_, v___y_27137__boxed_1647_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v_xs_1637_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t v___y_1649_, lean_object* v___f_1650_, lean_object* v_xs_1651_, lean_object* v_b_1652_, uint8_t v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; lean_object* v___f_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1660_ = lean_box(v___y_1649_);
lean_inc_ref(v_xs_1651_);
v___f_1661_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1661_, 0, v_b_1652_);
lean_closure_set(v___f_1661_, 1, v_xs_1651_);
lean_closure_set(v___f_1661_, 2, v___x_1660_);
v___x_1662_ = lean_box(v___y_1653_);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1657_);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
v___x_1663_ = lean_apply_9(v___f_1650_, v_xs_1651_, v___f_1661_, v___x_1662_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, lean_box(0));
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object* v_sz_1664_, lean_object* v_i_1665_, lean_object* v_bs_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
size_t v_sz_boxed_1674_; size_t v_i_boxed_1675_; uint8_t v___y_27176__boxed_1676_; lean_object* v_res_1677_; 
v_sz_boxed_1674_ = lean_unbox_usize(v_sz_1664_);
lean_dec(v_sz_1664_);
v_i_boxed_1675_ = lean_unbox_usize(v_i_1665_);
lean_dec(v_i_1665_);
v___y_27176__boxed_1676_ = lean_unbox(v___y_1667_);
v_res_1677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_boxed_1674_, v_i_boxed_1675_, v_bs_1666_, v___y_27176__boxed_1676_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
uint8_t v___y_27197__boxed_1688_; lean_object* v_res_1689_; 
v___y_27197__boxed_1688_ = lean_unbox(v___y_1681_);
v_res_1689_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_x_1678_, v_x_1679_, v_x_1680_, v___y_27197__boxed_1688_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object* v_as_1690_, lean_object* v_sz_1691_, lean_object* v_i_1692_, lean_object* v_b_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
size_t v_sz_boxed_1701_; size_t v_i_boxed_1702_; uint8_t v___y_27220__boxed_1703_; lean_object* v_res_1704_; 
v_sz_boxed_1701_ = lean_unbox_usize(v_sz_1691_);
lean_dec(v_sz_1691_);
v_i_boxed_1702_ = lean_unbox_usize(v_i_1692_);
lean_dec(v_i_1692_);
v___y_27220__boxed_1703_ = lean_unbox(v___y_1694_);
v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_as_1690_, v_sz_boxed_1701_, v_i_boxed_1702_, v_b_1693_, v___y_27220__boxed_1703_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v_as_1690_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object* v_00_u03b2_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_x_1706_, v_x_1707_, v_x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object* v_00_u03b2_1710_, lean_object* v_m_1711_, lean_object* v_a_1712_, lean_object* v_b_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_m_1711_, v_a_1712_, v_b_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object* v_00_u03b2_1715_, lean_object* v_m_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_m_1716_, v_a_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object* v_00_u03b2_1719_, lean_object* v_m_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_00_u03b2_1719_, v_m_1720_, v_a_1721_);
lean_dec_ref(v_a_1721_);
lean_dec_ref(v_m_1720_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object* v_00_u03b2_1723_, lean_object* v_x_1724_, size_t v_x_1725_, size_t v_x_1726_, lean_object* v_x_1727_, lean_object* v_x_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_1724_, v_x_1725_, v_x_1726_, v_x_1727_, v_x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_){
_start:
{
size_t v_x_27800__boxed_1736_; size_t v_x_27801__boxed_1737_; lean_object* v_res_1738_; 
v_x_27800__boxed_1736_ = lean_unbox_usize(v_x_1732_);
lean_dec(v_x_1732_);
v_x_27801__boxed_1737_ = lean_unbox_usize(v_x_1733_);
lean_dec(v_x_1733_);
v_res_1738_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(v_00_u03b2_1730_, v_x_1731_, v_x_27800__boxed_1736_, v_x_27801__boxed_1737_, v_x_1734_, v_x_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(lean_object* v_00_u03b2_1739_, lean_object* v_a_1740_, lean_object* v_x_1741_){
_start:
{
uint8_t v___x_1742_; 
v___x_1742_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_1740_, v_x_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1743_, lean_object* v_a_1744_, lean_object* v_x_1745_){
_start:
{
uint8_t v_res_1746_; lean_object* v_r_1747_; 
v_res_1746_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(v_00_u03b2_1743_, v_a_1744_, v_x_1745_);
lean_dec(v_x_1745_);
lean_dec_ref(v_a_1744_);
v_r_1747_ = lean_box(v_res_1746_);
return v_r_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6(lean_object* v_00_u03b2_1748_, lean_object* v_data_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(v_data_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7(lean_object* v_00_u03b2_1751_, lean_object* v_a_1752_, lean_object* v_b_1753_, lean_object* v_x_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_1752_, v_b_1753_, v_x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(lean_object* v_00_u03b2_1756_, lean_object* v_a_1757_, lean_object* v_x_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1757_, v_x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1760_, lean_object* v_a_1761_, lean_object* v_x_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(v_00_u03b2_1760_, v_a_1761_, v_x_1762_);
lean_dec(v_x_1762_);
lean_dec_ref(v_a_1761_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17(lean_object* v_00_u03b1_1764_, lean_object* v_x_1765_, uint8_t v_isExporting_1766_, uint8_t v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(v_x_1765_, v_isExporting_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___boxed(lean_object* v_00_u03b1_1775_, lean_object* v_x_1776_, lean_object* v_isExporting_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
uint8_t v_isExporting_boxed_1785_; uint8_t v___y_27832__boxed_1786_; lean_object* v_res_1787_; 
v_isExporting_boxed_1785_ = lean_unbox(v_isExporting_1777_);
v___y_27832__boxed_1786_ = lean_unbox(v___y_1778_);
v_res_1787_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17(v_00_u03b1_1775_, v_x_1776_, v_isExporting_boxed_1785_, v___y_27832__boxed_1786_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11(lean_object* v_00_u03b1_1788_, lean_object* v_x_1789_, uint8_t v_when_1790_, uint8_t v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(v_x_1789_, v_when_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___boxed(lean_object* v_00_u03b1_1799_, lean_object* v_x_1800_, lean_object* v_when_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
uint8_t v_when_boxed_1809_; uint8_t v___y_27855__boxed_1810_; lean_object* v_res_1811_; 
v_when_boxed_1809_ = lean_unbox(v_when_1801_);
v___y_27855__boxed_1810_ = lean_unbox(v___y_1802_);
v_res_1811_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11(v_00_u03b1_1799_, v_x_1800_, v_when_boxed_1809_, v___y_27855__boxed_1810_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_1812_, lean_object* v_n_1813_, lean_object* v_k_1814_, lean_object* v_v_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(v_n_1813_, v_k_1814_, v_v_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_1817_, size_t v_depth_1818_, lean_object* v_keys_1819_, lean_object* v_vals_1820_, lean_object* v_heq_1821_, lean_object* v_i_1822_, lean_object* v_entries_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_depth_1818_, v_keys_1819_, v_vals_1820_, v_i_1822_, v_entries_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_1825_, lean_object* v_depth_1826_, lean_object* v_keys_1827_, lean_object* v_vals_1828_, lean_object* v_heq_1829_, lean_object* v_i_1830_, lean_object* v_entries_1831_){
_start:
{
size_t v_depth_boxed_1832_; lean_object* v_res_1833_; 
v_depth_boxed_1832_ = lean_unbox_usize(v_depth_1826_);
lean_dec(v_depth_1826_);
v_res_1833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(v_00_u03b2_1825_, v_depth_boxed_1832_, v_keys_1827_, v_vals_1828_, v_heq_1829_, v_i_1830_, v_entries_1831_);
lean_dec_ref(v_vals_1828_);
lean_dec_ref(v_keys_1827_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_1834_, lean_object* v_i_1835_, lean_object* v_source_1836_, lean_object* v_target_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(v_i_1835_, v_source_1836_, v_target_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_, lean_object* v_x_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(v_x_1840_, v_x_1841_, v_x_1842_, v_x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16(lean_object* v_00_u03b2_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(v_x_1846_, v_x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__0(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_box(0);
v___x_1850_ = lean_unsigned_to_nat(16u);
v___x_1851_ = lean_mk_array(v___x_1850_, v___x_1849_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__1(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__0, &l_Lean_Meta_abstractNestedProofs___closed__0_once, _init_l_Lean_Meta_abstractNestedProofs___closed__0);
v___x_1853_ = lean_unsigned_to_nat(0u);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v___x_1852_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs(lean_object* v_e_1855_, uint8_t v_cache_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v___x_1862_; 
lean_inc_ref(v_e_1855_);
v___x_1862_ = l_Lean_Meta_isProof(v_e_1855_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1883_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1883_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1883_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
uint8_t v___x_1867_; 
v___x_1867_ = lean_unbox(v_a_1863_);
lean_dec(v_a_1863_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_del_object(v___x_1865_);
v___x_1868_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__1, &l_Lean_Meta_abstractNestedProofs___closed__1_once, _init_l_Lean_Meta_abstractNestedProofs___closed__1);
v___x_1869_ = lean_st_mk_ref(v___x_1868_);
v___x_1870_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1855_, v_cache_1856_, v___x_1869_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1879_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1879_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1879_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1875_ = lean_st_ref_get(v___x_1869_);
lean_dec(v___x_1869_);
lean_dec(v___x_1875_);
if (v_isShared_1874_ == 0)
{
v___x_1877_ = v___x_1873_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1871_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
lean_dec(v___x_1869_);
return v___x_1870_;
}
}
else
{
lean_object* v___x_1881_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v_e_1855_);
v___x_1881_ = v___x_1865_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_e_1855_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v_e_1855_);
v_a_1884_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1862_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1862_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object* v_e_1892_, lean_object* v_cache_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
uint8_t v_cache_boxed_1899_; lean_object* v_res_1900_; 
v_cache_boxed_1899_ = lean_unbox(v_cache_1893_);
v_res_1900_ = l_Lean_Meta_abstractNestedProofs(v_e_1892_, v_cache_boxed_1899_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
return v_res_1900_;
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
